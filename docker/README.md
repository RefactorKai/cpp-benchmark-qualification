# Pinned Gate 1 Sandbox Environment

[`gate1.Dockerfile`](gate1.Dockerfile) pins the isolated C++17 execution environment used by `development/paired_study/expansion_run.py` and `development/gate1_sandbox.py`:

- **Base OS:** `ubuntu:26.04@sha256:d66b366dc2208328ce2aa6fe174e2ee04de0cac2cf6feb64ef003a2bc37dd871` (signed Ubuntu archive snapshot as of `2026-11-05` UTC)
- **Toolchain & Isolation:** `GCC 15.2.0` (`-std=c++17`), `Bubblewrap 0.11.1`, `systemd 259` (`systemd-run --user --scope` cgroup v2 resource accounting), `Python 3.14`

## Offline Replay vs. Container Execution

Public verification and full per-point statistical replay run directly on the host with Python `>= 3.11` stdlib (`0` container dependencies):

```sh
python -B verify.py --figures --pdf
python -B -m pytest -q
```

To build the pinned Gate 1 container image on an `x86_64` Linux host with Docker, cgroup v2, and non-root user namespaces enabled:

```sh
docker build -f docker/gate1.Dockerfile -t cpp-benchmark-qualification-gate1 .
```

`systemd` runs as PID 1 inside the container so the non-root user manager receives the CPU, cpuset, I/O, memory, and PID controllers for unmodified `development/gate1_sandbox.py` runs (`prlimit --cpu=8:8` and FD `199` counter wire). Because the outer `systemd` boot requires a privileged container, run only on a disposable VM with container networking disabled (`--network none`). Upstream C++ source payloads and private S2–S5 fixture bundles are not distributed in this repository; public reproduction replays the recorded counter traces in `data/anonymous-measurements.json` (`c2ba8209...`).
