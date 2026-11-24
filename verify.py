"""Stdlib-only integrity, leak-audit, and deterministic replay verifier."""

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


def check_replay_and_macros() -> None:
    with TemporaryDirectory() as tmp:
        tmp_dir = Path(tmp)
        tmp_slots = tmp_dir / "benchmark_slots.tex"
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
                "--write-slots",
                str(tmp_slots),
                "--out",
                str(tmp_receipt),
            ],
            check=True,
        )
        got_slots = tmp_slots.read_bytes().replace(b"\r\n", b"\n")
        exp_slots = (ROOT / "manuscript/benchmark_slots.tex").read_bytes().replace(b"\r\n", b"\n")
        if got_slots != exp_slots:
            raise ValueError("Replayed benchmark_slots.tex differs from manuscript/benchmark_slots.tex")

        got_receipt = json.loads(tmp_receipt.read_bytes())
        exp_receipt = json.loads((ROOT / "data/final_receipt.json").read_bytes())
        if got_receipt != exp_receipt:
            raise ValueError("Replayed final_receipt.json differs from data/final_receipt.json")

    tex_src = (ROOT / "manuscript/paired_mechanism.tex").read_text(encoding="utf-8")
    tex_src = re.sub(r"(?<!\\)%[^\n]*", "", tex_src)
    slots_src = (ROOT / "manuscript/benchmark_slots.tex").read_text(encoding="utf-8")
    grouped_src = (ROOT / "manuscript/grouped_statistics_macros.tex").read_text(encoding="utf-8")

    body_after_def = "\n".join(slots_src.splitlines()[21:])
    if r"\BenchSlot{" in body_after_def or r"\BenchCell" in body_after_def:
        raise ValueError("Unfilled placeholder slot remains in manuscript/benchmark_slots.tex")

    used_bench = set(re.findall(r"\\(Bench[A-Za-z0-9]+)", tex_src))
    def_bench = set(re.findall(r"\\newcommand\{\\(Bench[A-Za-z0-9]+)\}", slots_src))
    if used_bench - def_bench:
        raise ValueError(f"Missing Bench macros: {sorted(used_bench - def_bench)}")

    used_grouped = set(re.findall(r"\\(Grouped[A-Za-z0-9]+)", tex_src))
    def_grouped = set(re.findall(r"\\newcommand\{\\(Grouped[A-Za-z0-9]+)\}", grouped_src))
    if used_grouped - def_grouped:
        raise ValueError(f"Missing Grouped macros: {sorted(used_grouped - def_grouped)}")


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
        for needle in ("Overfull", "Undefined", "Warning"):
            if needle in log:
                raise ValueError(f"LaTeX log contains {needle!r}")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--figures", action="store_true", help="Regenerate publication figures in a temp dir.")
    parser.add_argument("--pdf", action="store_true", help="Compile paired_mechanism.pdf cleanly with pdflatex+bibtex.")
    args = parser.parse_args(argv)

    n_files = check_sha256sums()
    check_quarantine_and_leaks()
    check_replay_and_macros()
    msg = f"Verified {n_files} SHA256SUMS, held_out_used=false, 0 ID leaks, and exact replay/macros."
    if args.figures:
        build_figures()
        msg += " Figures OK."
    if args.pdf:
        build_pdf()
        msg += " PDF compile OK (0 warnings/overfulls)."
    print(msg)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
