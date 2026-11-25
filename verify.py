"""Stdlib-only integrity, leak-audit, claims-ledger, literal-guard, and replay verifier."""

from __future__ import annotations

import argparse
from hashlib import sha256
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
from tempfile import TemporaryDirectory

ROOT = Path(__file__).resolve().parent
LEAK_RE = re.compile(r"\b(?:p\d{5}|s\d{9})\b")
BANNED_PROSE_RE = re.compile(r"\b(?:registered|asymptotic(?:ally)?)\b|github\.com/(?!evalplus\b)", re.IGNORECASE)


def check_sha256sums() -> int:
    sums_path = ROOT / "SHA256SUMS.txt"
    lines = [ln.strip() for ln in sums_path.read_text(encoding="utf-8").splitlines() if ln.strip()]
    if not lines:
        raise ValueError("SHA256SUMS.txt is empty")
    for ln in lines:
        expected, rel = ln.split(None, 1)
        target = ROOT / rel
        if not target.is_file():
            raise FileNotFoundError(f"Missing verified file: {rel}")
        actual = sha256(target.read_bytes()).hexdigest()
        if actual != expected:
            raise ValueError(f"SHA-256 mismatch for {rel}: {actual} != {expected}")
    return len(lines)


def check_quarantine_and_leaks() -> None:
    manifest = json.loads((ROOT / "data/freeze/manifest-expanded.json").read_bytes())
    if manifest.get("held_out_used") is not False:
        raise ValueError(f"Expected held_out_used=false, got {manifest.get('held_out_used')!r}")

    for path in sorted((ROOT / "data").glob("*.json")) + sorted(
        p for ext in ("*.tex", "*.bib") for p in (ROOT / "manuscript").glob(ext)
    ):
        hits = LEAK_RE.findall(path.read_text(encoding="utf-8"))
        if hits:
            raise ValueError(f"Unredacted ID found in {path.relative_to(ROOT)}: {hits[:5]}")


def verify_tex_literals_and_banned_terms(tex_raw: str) -> None:
    """Reject any unguarded empirical digit or banned overclaim term in manuscript body."""
    if r"\begin{document}" not in tex_raw or r"\end{document}" not in tex_raw:
        raise ValueError("manuscript TeX missing \\begin{document} or \\end{document}")
    body = tex_raw.split(r"\begin{document}", 1)[1].split(r"\end{document}", 1)[0]
    body = re.sub(r"(?<!\\)%[^\n]*", "", body)
    body = re.sub(r"\\(?:cite|label|ref|bibliographystyle|bibliography)\{[^}]*\}", "", body)
    body = re.sub(r"\\includegraphics(?:\[[^\]]*\])?\{[^}]*\}", "", body)
    body = re.sub(r"(?m)^\\begin\{tabularx\}\{[^\n]*$", "", body)

    banned_hits = BANNED_PROSE_RE.findall(body)
    if banned_hits:
        raise ValueError(f"Banned overclaim or non-anonymous term in manuscript body: {banned_hits[:5]}")

    cleaned = body
    for pat in (
        r"\\(?:Bench|Grouped)[A-Za-z0-9]+",
        r"\bDefects4J\b",
        r"Gate~1",
        r"Amendments?~[1-5](?:--[1-5])?",
        r"Section~1[01]",
        r"Stage~S[0-5]",
        r"\bS(?:1[0-4]|[0-9])\b",
        r"\bP[1-3]\b",
        r"-O[023]",
        r"\bc_[01]\b",
        r"R\^2",
        r"95\\%",
        r"\b0\.05\b",
    ):
        cleaned = re.sub(pat, "", cleaned)

    stray_digits = re.findall(r"\d+(?:[.,]\d+)?", cleaned)
    if stray_digits:
        raise ValueError(f"Unguarded numeric literal(s) in paired_mechanism.tex: {stray_digits[:10]}")


def verify_paper_claims(claims: dict, slots_src: str, grouped_src: str, tex_src: str) -> int:
    if claims.get("schema") != "eapg.expansion.paper_claims.v1":
        raise ValueError(f"Invalid paper_claims.json schema: {claims.get('schema')!r}")
    if claims.get("held_out_used") is not False:
        raise ValueError("paper_claims.json must assert held_out_used=false")

    entries = claims.get("claims")
    if not isinstance(entries, list) or not entries or len(entries) != claims.get("claim_count"):
        raise ValueError("paper_claims.json claim_count mismatch")

    slot_defs = {
        m.group(1): m.group(2)
        for ln in slots_src.splitlines()
        if (m := re.match(r"^\\newcommand\{\\(Bench[A-Za-z0-9]+)\}(?:\[\d+\])?\{(.*)\}$", ln.strip()))
        and m.group(1) not in ("BenchSlot", "BenchCell")
    }
    grouped_defs = {
        m.group(1): m.group(2)
        for ln in grouped_src.splitlines()
        if (m := re.match(r"^\\newcommand\{\\(Grouped[A-Za-z0-9]+)\}\{(.+)\}$", ln.strip()))
    }
    tex_clean = re.sub(r"(?<!\\)%[^\n]*", "", tex_src)
    used_grouped = set(re.findall(r"\\(Grouped[A-Za-z0-9]+)", tex_clean))
    expected_macros = set(slot_defs) | used_grouped

    by_macro = {c["macro"]: c for c in entries}
    if len(by_macro) != len(entries) or set(by_macro) != expected_macros:
        missing = sorted(expected_macros - set(by_macro))
        extra = sorted(set(by_macro) - expected_macros)
        raise ValueError(f"paper_claims.json macro coverage mismatch: missing={missing}, extra={extra}")

    for macro, item in by_macro.items():
        if item.get("evidence_class") not in ("re-executable", "replay-only"):
            raise ValueError(f"Disallowed or private-only evidence_class on {macro}: {item.get('evidence_class')!r}")
        if not isinstance(item.get("instrument"), str) or not item["instrument"].strip():
            raise ValueError(f"Missing instrument on {macro}")
        srcs = item.get("source_sha256")
        if not isinstance(srcs, list) or not srcs or not all(isinstance(s, str) and re.fullmatch(r"[0-9a-f]{64}", s) for s in srcs):
            raise ValueError(f"Invalid source_sha256 list on {macro}")
        exp_val = slot_defs[macro] if macro in slot_defs else grouped_defs[macro]
        if item.get("rendered_tex") != exp_val:
            raise ValueError(f"paper_claims.json rendered_tex mismatch on {macro}")
    return len(entries)


def check_replay_and_macros() -> int:
    with TemporaryDirectory() as tmp:
        tmp_dir = Path(tmp)
        tmp_slots = tmp_dir / "benchmark_slots.tex"
        tmp_claims = tmp_dir / "paper_claims.json"
        tmp_receipt = tmp_dir / "final_receipt.json"
        subprocess.run(
            [
                sys.executable,
                "-B",
                str(ROOT / "analysis/expansion_analyze.py"),
                "--aggregate-json",
                str(ROOT / "data/final-a5-stats-agg.json"),
                "--author-check",
                str(ROOT / "data/author-check-50-agg.json"),
                "--forensics-json",
                str(ROOT / "data/alert-and-fit-forensics-agg.json"),
                "--anon-measurements",
                str(ROOT / "data/anonymous-measurements.json"),
                "--write-slots",
                str(tmp_slots),
                "--write-claims",
                str(tmp_claims),
                "--out",
                str(tmp_receipt),
            ],
            check=True,
        )
        got_slots = tmp_slots.read_bytes().replace(b"\r\n", b"\n")
        exp_slots = (ROOT / "manuscript/benchmark_slots.tex").read_bytes().replace(b"\r\n", b"\n")
        if got_slots != exp_slots:
            raise ValueError("Replayed benchmark_slots.tex differs from manuscript/benchmark_slots.tex")

        got_claims = json.loads(tmp_claims.read_bytes())
        exp_claims = json.loads((ROOT / "data/paper_claims.json").read_bytes())
        if got_claims != exp_claims:
            raise ValueError("Replayed paper_claims.json differs from data/paper_claims.json")

        got_receipt = json.loads(tmp_receipt.read_bytes())
        exp_receipt = json.loads((ROOT / "data/final_receipt.json").read_bytes())
        if got_receipt != exp_receipt:
            raise ValueError("Replayed final_receipt.json differs from data/final_receipt.json")

    tex_raw = (ROOT / "manuscript/paired_mechanism.tex").read_text(encoding="utf-8")
    tex_src = re.sub(r"(?<!\\)%[^\n]*", "", tex_raw)
    slots_src = (ROOT / "manuscript/benchmark_slots.tex").read_text(encoding="utf-8")
    grouped_src = (ROOT / "manuscript/grouped_statistics_macros.tex").read_text(encoding="utf-8")

    body_after_def = "\n".join(slots_src.splitlines()[21:])
    if r"\BenchSlot{" in body_after_def or r"\BenchCell" in body_after_def:
        raise ValueError("Unfilled placeholder slot remains in manuscript/benchmark_slots.tex")

    used_bench = set(re.findall(r"\\(Bench[A-Za-z0-9]+)", tex_src))
    def_bench = set(re.findall(r"\\newcommand\{\\(Bench[A-Za-z0-9]+)\}", slots_src))
    if used_bench - def_bench:
        raise ValueError(f"Missing Bench macros: {sorted(used_bench - def_bench)}")
    orphan_bench = (def_bench - used_bench) - {"BenchSlot", "BenchCell"}
    if orphan_bench:
        raise ValueError(f"Orphan Bench macros: {sorted(orphan_bench)}")

    used_grouped = set(re.findall(r"\\(Grouped[A-Za-z0-9]+)", tex_src))
    def_grouped = set(re.findall(r"\\newcommand\{\\(Grouped[A-Za-z0-9]+)\}", grouped_src))
    if used_grouped - def_grouped:
        raise ValueError(f"Missing Grouped macros: {sorted(used_grouped - def_grouped)}")

    verify_tex_literals_and_banned_terms(tex_raw)
    return verify_paper_claims(exp_claims, slots_src, grouped_src, tex_raw)


def build_figures() -> None:
    with TemporaryDirectory() as tmp:
        out_dir = Path(tmp) / "figures"
        subprocess.run(
            [
                sys.executable,
                "-B",
                str(ROOT / "analysis/generate_figures.py"),
                "--receipt",
                str(ROOT / "data/final_receipt.json"),
                "--out-dir",
                str(out_dir),
            ],
            check=True,
        )
        for name in ("fig_s1_desk_taxonomy.pdf", "fig_qualification_outcomes.pdf"):
            if not (out_dir / name).is_file():
                raise FileNotFoundError(f"Figure not generated: {name}")


def build_pdf() -> None:
    if not (shutil.which("pdflatex") and shutil.which("bibtex")):
        raise RuntimeError("pdflatex and bibtex are required for --pdf verification")
    with TemporaryDirectory() as tmp:
        tmp_dir = Path(tmp)
        for p in (ROOT / "manuscript").iterdir():
            if p.is_file() and p.suffix in (".tex", ".bib", ".pdf"):
                shutil.copy2(p, tmp_dir / p.name)
        for cmd in (
            ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "paired_mechanism.tex"],
            ["bibtex", "paired_mechanism"],
            ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "paired_mechanism.tex"],
            ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "paired_mechanism.tex"],
        ):
            subprocess.run(cmd, cwd=tmp_dir, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        log = (tmp_dir / "paired_mechanism.log").read_text(encoding="utf-8", errors="ignore")
        for needle in ("Overfull", "Underfull", "Undefined", "Warning"):
            if needle in log:
                raise ValueError(f"LaTeX log contains {needle!r}")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--figures", action="store_true", help="Regenerate publication figures in a temp dir.")
    parser.add_argument("--pdf", action="store_true", help="Compile paired_mechanism.pdf cleanly with pdflatex+bibtex.")
    args = parser.parse_args(argv)

    n_files = check_sha256sums()
    check_quarantine_and_leaks()
    n_claims = check_replay_and_macros()
    msg = (
        f"Verified {n_files} SHA256SUMS, held_out_used=false, 0 ID leaks, "
        f"{n_claims} guarded claims, 0 unguarded literals, and exact replay."
    )
    if args.figures:
        build_figures()
        msg += " Figures OK."
    if args.pdf:
        build_pdf()
        msg += " PDF compile OK (0 warnings/overfulls/underfulls)."
    print(msg)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
