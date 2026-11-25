"""Stdlib-only checksum, de-identification, claims-ledger, macro-consistency, and replay verifier."""

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
EXPECTED_FIGURES = (
    "fig_pipeline_funnel.pdf",
    "fig_s1_desk_taxonomy.pdf",
    "fig_scaling_landscape.pdf",
    "fig_alert_trajectories.pdf",
    "fig_manski_tipping.pdf",
)


def check_sha256sums() -> dict[str, str]:
    sums_path = ROOT / "SHA256SUMS.txt"
    lines = [ln.strip() for ln in sums_path.read_text(encoding="utf-8").splitlines() if ln.strip()]
    if not lines:
        raise ValueError("SHA256SUMS.txt is empty")
    verified: dict[str, str] = {}
    for ln in lines:
        expected, rel = ln.split(None, 1)
        target = ROOT / rel
        if not target.is_file():
            raise FileNotFoundError(f"Missing verified file: {rel}")
        actual = sha256(target.read_bytes()).hexdigest()
        if actual != expected:
            raise ValueError(f"SHA-256 mismatch for {rel}: {actual} != {expected}")
        verified[rel] = actual
    if (ROOT / ".git").exists() and shutil.which("git"):
        tracked = subprocess.check_output(
            ["git", "-C", str(ROOT), "ls-files"],
            text=True,
            encoding="utf-8",
        ).splitlines()
        missing = sorted(
            f for f in tracked
            if f != "SHA256SUMS.txt" and (ROOT / f).is_file() and f not in verified
        )
        if missing:
            raise ValueError(f"Tracked files omitted from SHA256SUMS.txt: {missing[:10]}")
    return verified


def check_quarantine_and_leaks() -> None:
    manifest = json.loads((ROOT / "data/freeze/manifest-expanded.json").read_bytes())
    if manifest.get("held_out_used") is not False:
        raise ValueError(f"Expected held_out_used=false, got {manifest.get('held_out_used')!r}")

    scan_paths = (
        sorted((ROOT / "data").glob("*.json"))
        + sorted(p for ext in ("*.tex", "*.bib") for p in (ROOT / "manuscript").glob(ext))
        + sorted((ROOT / "analysis").glob("*.py"))
        + sorted((ROOT / "tests").glob("*.py"))
        + [ROOT / "README.md"]
    )
    for path in scan_paths:
        hits = LEAK_RE.findall(path.read_text(encoding="utf-8"))
        if hits:
            raise ValueError(f"Unredacted ID found in {path.relative_to(ROOT)}: {hits[:5]}")


def verify_tex_literals_and_banned_terms(tex_raw: str) -> None:
    """Reject unmacroed empirical digits or prohibited overclaim terms in the manuscript body."""
    if r"\begin{document}" not in tex_raw or r"\end{document}" not in tex_raw:
        raise ValueError("manuscript TeX missing \\begin{document} or \\end{document}")
    body = tex_raw.split(r"\begin{document}", 1)[1].split(r"\end{document}", 1)[0]
    body = re.sub(r"(?<!\\)%[^\n]*", "", body)
    body = re.sub(r"\\(?:cite|label|ref|eqref|bibliographystyle|bibliography)\{[^}]*\}", "", body)
    body = re.sub(r"\\includegraphics(?:\[[^\]]*\])?\{[^}]*\}", "", body)
    body = re.sub(r"(?m)^\\begin\{tabular[x*]\}\{[^\n]*$", "", body)
    body = re.sub(r"\\begin\{minipage\}\[t\]\{[0-9.]+\\linewidth\}", "", body)
    body = re.sub(r"\\setlength\{[^}]*\}\{[^}]*\}", "", body)
    body = re.sub(r"\\renewcommand\{\\arraystretch\}\{[0-9.]+\}", "", body)
    body = re.sub(r"\\addlinespace\[[0-9.]+pt\]", "", body)
    body = re.sub(r"\\setcounter\{table\}\{0\}", "", body)
    body = re.sub(r"\\multicolumn\{\d+\}", "", body)
    body = re.sub(r"\\hspace\*?\{[0-9.]+(?:em|pt)\}", "", body)
    body = re.sub(r"\\\\\[[0-9.]+pt\]", "", body)
    body = re.sub(r"\\dimexpr\\linewidth-2\\fboxsep-2\\fboxrule\\relax", "", body)

    banned_hits = BANNED_PROSE_RE.findall(body)
    if banned_hits:
        raise ValueError(f"Banned overclaim or non-anonymous term in manuscript body: {banned_hits[:5]}")

    cleaned = body
    for pat in (
        r"\\(?:Bench|Grouped)[A-Za-z0-9]+(?:\{\})?",
        r"5\(T_0\(n\)-R_0\(n\)\)\s*\\ge\s*4\(T_0\(n\)-Q_0\(n\)\)",
        r"\bDefects4J\b",
        r"(?:-std=c\+\+17|C\+\+17)",
        r"SHA-256",
        r"SHA256SUMS\.txt",
        r"Amendment[-~][1-5]",
        r"s1\\_author\\_check\\_draw\.json",
        r"Gate~1",
        r"\bRQ[1-4](?:--RQ[1-4])?\b",
        r"Zone[-~][1-3]",
        r"Rule~[1-5]",
        r"Listing~1",
        r"Section~1[01]",
        r"§9",
        r"\\S9",
        r"\\S1[01]",
        r"Stage~S[0-5]",
        r"\bSA(?:1[0-4]|[1-9])(?:a/b|[ab])?(?:--SA(?:1[0-4]|[1-9])b?)?\b",
        r"\bS(?:1[0-4]|[0-5])(?:--S(?:1[0-4]|[0-5]))?\b",
        r"\bP[1-3](?:--P[1-3])?\b",
        r"\bB[0-5](?:--B[0-5])?\b",
        r"\bW[1-3](?:--W[1-3])?\b",
        r"\bHolm-[35]\b",
        r"\b1-S\b",
        r"\bAC1\b",
        r"\b3-Bkt\b",
        r"\b[12]D\b",
        r"exit[-~ ](?:0|1|137)\b",
        r"ubsan\\_only\\_stack\\_8mb",
        r"O0==O2==O3",
        r"O2==O3",
        r"O0/O2/O3",
        r"-?O[023]\b",
        r"\([1-3]\)~",
        r"95\\%",
        r"50\\%",
        r"\(1-0\.05\)\^2",
        r"\b0\.05\b",
        r"2\^\{64\}",
        r"5N\^2",
        r"O\(N\^3\)",
        r"\\chi(?:\^2_3|_3(?:\^2)?)",
        r"\\text\{df\}\s*=\s*3",
        r"R\^2(?:\s*=\s*1\.000)?",
        r"D_\{\\max\}\s*>\s*1\.5",
        r"Q_0\{=\}0",
        r"c\\_0\+\+",
        r"\b[cTQRH]_[01]\b",
        r"\blong\s+Q0\s*=\s*1\b",
        r"\b[cTQR][01]\b",
        r"\bD_6\b",
        r"\bk=6\b",
        r"\bq=3\b",
        r"\bi=1\b",
        r"\bi=0\b",
        r"\bj=0\b",
        r"\bn_1\b",
        r"n_\{k-1\}",
        r"\\Delta_\{\\text\{2-step\}\}",
        r"(?:y\s*=\s*|\\le\s*)0\.08",
        r"\\ll\s*1\b",
        r"<\s*5\b",
        r"3\\times 3",
        r"2\\times 2",
        r"1,\\dots,",
        r"1/\\ln\s+n",
        r"\[0,\s*1\]",
        r"n\(n\+1\)/2",
        r"O\(1\)",
        r"1\s*\+\s*y",
        r"\^2",
        r"\\text\{-O2\}",
        r"(?:<|=|>|\\le|\\ge)\s*0\b",
    ):
        cleaned = re.sub(pat, "", cleaned)

    stray_digits = re.findall(r"\d+(?:[.,]\d+)?", cleaned)
    if stray_digits:
        raise ValueError(f"Unguarded numeric literal(s) in paired_mechanism.tex: {stray_digits[:10]}")


def verify_paper_claims(
    claims: dict,
    slots_src: str,
    grouped_src: str,
    tex_src: str,
    *,
    known_shas: set[str] | None = None,
) -> int:
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
    orphan_grouped = set(grouped_defs) - used_grouped
    if orphan_grouped:
        raise ValueError(f"Orphan Grouped macros: {sorted(orphan_grouped)}")
    expected_macros = set(slot_defs) | used_grouped

    by_macro = {c["macro"]: c for c in entries}
    if len(by_macro) != len(entries) or set(by_macro) != expected_macros:
        missing = sorted(expected_macros - set(by_macro))
        extra = sorted(set(by_macro) - expected_macros)
        raise ValueError(f"paper_claims.json macro coverage mismatch: missing={missing}, extra={extra}")

    for macro, item in by_macro.items():
        if item.get("evidence_class") not in ("protocol-constant", "re-executable", "replay-only"):
            raise ValueError(f"Disallowed or private-only evidence_class on {macro}: {item.get('evidence_class')!r}")
        if not isinstance(item.get("instrument"), str) or not item["instrument"].strip():
            raise ValueError(f"Missing instrument on {macro}")
        srcs = item.get("source_sha256")
        if not isinstance(srcs, list) or not srcs or not all(isinstance(s, str) and re.fullmatch(r"[0-9a-f]{64}", s) for s in srcs):
            raise ValueError(f"Invalid source_sha256 list on {macro}")
        if known_shas is not None:
            unresolved = [s for s in srcs if s not in known_shas]
            if unresolved:
                raise ValueError(f"Unresolved source_sha256 on {macro}: {unresolved}")
        exp_val = slot_defs[macro] if macro in slot_defs else grouped_defs[macro]
        if item.get("rendered_tex") != exp_val:
            raise ValueError(f"paper_claims.json rendered_tex mismatch on {macro}")
    return len(entries)


def check_replay_and_macros(verified_files: dict[str, str] | None = None) -> int:
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
                "--manifest",
                str(ROOT / "data/freeze/manifest-expanded.json"),
                "--grouped-macros",
                str(ROOT / "manuscript/grouped_statistics_macros.tex"),
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

    body_after_def = slots_src.split(r"\newcommand{\BenchCell}", 1)[1].split("\n", 1)[1]
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
    orphan_grouped = def_grouped - used_grouped
    if orphan_grouped:
        raise ValueError(f"Orphan Grouped macros: {sorted(orphan_grouped)}")

    verify_tex_literals_and_banned_terms(tex_raw)
    known_shas = set(verified_files.values()) if verified_files is not None else None
    return verify_paper_claims(exp_claims, slots_src, grouped_src, tex_raw, known_shas=known_shas)


def build_figures(out_dir: Path) -> None:
    subprocess.run(
        [
            sys.executable,
            "-B",
            str(ROOT / "analysis/generate_figures.py"),
            "--receipt",
            str(ROOT / "data/final_receipt.json"),
            "--anon-measurements",
            str(ROOT / "data/anonymous-measurements.json"),
            "--forensics-json",
            str(ROOT / "data/alert-and-fit-forensics-agg.json"),
            "--out-dir",
            str(out_dir),
        ],
        check=True,
    )
    has_pdftoppm = shutil.which("pdftoppm") is not None
    with TemporaryDirectory() as raster_tmp:
        raster_dir = Path(raster_tmp)
        for name in EXPECTED_FIGURES:
            gen_pdf = out_dir / name
            if not gen_pdf.is_file() or gen_pdf.stat().st_size == 0:
                raise FileNotFoundError(f"Figure not generated: {name}")
            ref_pdf = ROOT / "manuscript" / name
            if has_pdftoppm and ref_pdf.is_file():
                stem = Path(name).stem
                gen_png = raster_dir / f"gen_{stem}"
                ref_png = raster_dir / f"ref_{stem}"
                subprocess.run(["pdftoppm", "-png", "-r", "150", "-singlefile", str(gen_pdf), str(gen_png)], check=True)
                subprocess.run(["pdftoppm", "-png", "-r", "150", "-singlefile", str(ref_pdf), str(ref_png)], check=True)
                if gen_png.with_suffix(".png").read_bytes() != ref_png.with_suffix(".png").read_bytes():
                    raise ValueError(f"Regenerated figure differs visually from manuscript/{name}")


def build_pdf(fig_dir: Path | None = None) -> None:
    if not (shutil.which("pdflatex") and shutil.which("bibtex")):
        raise RuntimeError("pdflatex and bibtex are required for --pdf verification")
    with TemporaryDirectory() as tmp:
        tmp_dir = Path(tmp)
        for p in (ROOT / "manuscript").iterdir():
            if p.is_file() and p.suffix in (".tex", ".bib", ".pdf"):
                shutil.copy2(p, tmp_dir / p.name)
        if fig_dir is not None:
            for name in EXPECTED_FIGURES:
                shutil.copy2(fig_dir / name, tmp_dir / name)
        for cmd in (
            ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "paired_mechanism.tex"],
            ["bibtex", "paired_mechanism"],
            ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "paired_mechanism.tex"],
            ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "paired_mechanism.tex"],
            ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "paired_mechanism.tex"],
        ):
            subprocess.run(cmd, cwd=tmp_dir, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        log = (tmp_dir / "paired_mechanism.log").read_text(encoding="utf-8", errors="ignore")
        for needle in ("Overfull", "Underfull", "Undefined", "Warning", ".pk"):
            if needle in log:
                raise ValueError(f"LaTeX log contains {needle!r}")
        blg = (tmp_dir / "paired_mechanism.blg").read_text(encoding="utf-8", errors="ignore")
        if "Warning--" in blg or "error message" in blg.lower():
            raise ValueError("BibTeX log contains warnings or errors")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--figures", action="store_true", help="Regenerate publication figures in a temporary directory and verify raster parity.")
    parser.add_argument("--pdf", action="store_true", help="Compile paired_mechanism.pdf with pdflatex and bibtex and check build logs.")
    args = parser.parse_args(argv)

    verified_files = check_sha256sums()
    check_quarantine_and_leaks()
    n_claims = check_replay_and_macros(verified_files)
    msg = (
        f"Verified {len(verified_files)} SHA256SUMS entries, held_out_used=false, 0 identifier leaks, "
        f"{n_claims} provenance-linked claims, and exact replay."
    )
    with TemporaryDirectory() as fig_tmp:
        fig_dir: Path | None = None
        if args.figures:
            fig_dir = Path(fig_tmp) / "figures"
            build_figures(fig_dir)
            msg += f" Regenerated and verified {len(EXPECTED_FIGURES)} figures."
        if args.pdf:
            build_pdf(fig_dir=fig_dir)
            msg += " Compiled paired_mechanism.pdf cleanly."
    print(msg)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
