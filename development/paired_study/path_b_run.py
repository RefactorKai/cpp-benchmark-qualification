"""Compiler optimization and instrumentation modes for isolated Gate 1 runs."""

MODES = {
    "plain": (),
    "ubsan": ("-fsanitize=undefined", "-fno-sanitize-recover=undefined"),
    **{flag: ("-" + flag, "-DPATH_B_COUNT") for flag in ("O0", "O2", "O3")},
}
