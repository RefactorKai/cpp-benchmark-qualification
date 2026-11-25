# Pinned Gate 1 Sandbox & Verification Environment

[`gate1.Dockerfile`](gate1.Dockerfile) pins the isolated C++17 execution and verification environment used alongside `development/paired_study/expansion_run.py` (`04f1a1b2...`) and `development/gate1_sandbox.py` (`7f9bf00a...`), superseding the legacy `development/run_sandbox_container.sh` wrapper referenced in the byte-frozen `expansion_run.py` docstring:

- **Base OS:** `ubuntu:26.04@sha256:d66b366dac61b575bee2aef07e9c26e8070096fbe84a3d4d3eb0da069b5d76db` (signed Ubuntu archive snapshot as of `2026-11-05` UTC)
- **Toolchain & Isolation:** `GCC 15.2.0` (`-std=c++17`), `Bubblewrap 0.11.1`, `systemd 259` (`systemd-run --user --scope` cgroup v2 accounting), `Python 3.14`, `matplotlib 3.10.1`, `numpy 2.2.4`, `pytest 9.0.2`, TeX Live, and `poppler-utils`

## Host or Unprivileged Container Verification

Checksum verification and statistical replay run with Python `>= 3.11` stdlib only (`--figures` and `--pdf` additionally require `matplotlib`, `numpy`, and TeX Live):

```sh
python -B verify.py
python -B verify.py --figures --pdf
python -B -m pytest -q
```

To build the image and run the entire verification suite (including figures and PDF compilation) without privilege or systemd PID 1:

```sh
docker build -f docker/gate1.Dockerfile -t cpp-benchmark-qualification-gate1 .
docker run --rm --network none --entrypoint "" -v "$PWD:/workspace" -w /workspace \
  cpp-benchmark-qualification-gate1 sh -c "python -B verify.py --figures --pdf && python -B -m pytest -q"
```

## Full Gate 1 C++ Isolation Mode

When booted with its default `CMD ["/sbin/init"]`, `systemd` runs as PID 1 so the non-root user manager receives the CPU, cpuset, I/O, memory, and PID controllers required by `development/gate1_sandbox.py` (`prlimit --cpu=8:8 --as=536870912:536870912` and the bind-mounted regular file opened on `FD 3` via `EAPG_COUNTER_FD`). Because booting `systemd` inside Docker requires a privileged container, run full Gate 1 mode only inside a disposable Linux VM with networking disabled (`--network none`).

Optional Linux/VM smoke test inside a booted container as user `eapg` (verifying `bwrap` + `systemd-run` + `FD 3` counter capture on a toy C++17 binary):

```sh
python -B -c "
from development import gate1_sandbox as gs
src = b'#include <cstdio>\nint main(){ puts(\"ok\"); FILE *f = fdopen(3, \"w\"); if(f){ fprintf(f, \"1 2\\n\"); fclose(f); } return 0; }\n'
c = gs.invoke(['/bin/sh', '-ec', 'g++ -std=c++17 -O2 -x c++ - -o /tmp/p; exec cat /tmp/p'], stdin_bytes=src, cpu_s=8, wall_s=25)
assert c['returncode'] == 0
r = gs.execute(c['stdout'], stdin_bytes=b'', cpu_s=8, wall_s=12, capture_counter=True)
assert r['returncode'] == 0 and r['stdout'].strip() == b'ok' and r['counter'].strip() == b'1 2'
print('GATE1_SMOKE_OK', r['cpu_usage_usec'])
"
```

Upstream C++ source payloads and execution harnesses remain offline; host verification replays the recorded counter traces in `data/anonymous-measurements.json` (`c2ba8209...`).
