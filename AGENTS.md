# AGENTS.md

Guidance for AI coding agents (Claude Code, Cursor, Aider, etc.) working in this repository. Humans should read this too — it summarizes how this fork is built, tested, and worked on.

## What this repo is

[YosysHQ/yosys](https://github.com/YosysHQ/yosys) — an open-source RTL synthesis framework — forked at `crockpotveggies/yosys`. Active branch: `crockpot/optimization-v1`, focused on performance optimization (~1.85× geomean over upstream `main` across the four benchmarks in `benchmark-results/generated/`).

## Build

This is an MSYS2-64 / mingw-w64 build on Windows. Build settings live in `Makefile.conf` (no abc, no zlib, no tcl, no plugins).

```bash
make -j6 yosys.exe
./yosys.exe -V
```

**Caveat for this Windows config:** the standard link step fails with `cannot find techlibs/quickl: No such file or directory` because the command line for 330 .o files exceeds Windows' limit. After `make -j6` reports that error, finish the link via response file:

```bash
bash benchmark-results/gen_objs.sh   # regenerate yosys_objs.txt with current GIT_REV
bash benchmark-results/link_yosys.sh # link via mingw response file
```

**After any change to `RTLIL::Module` layout** (adding/removing fields), force-clean stale .o files first — the `.d` dependency files in `passes/opt/opt_clean/` and `libs/*` don't track `kernel/rtlil.h`, so stale .o files cause silent ABI mismatch and SEGVs in unrelated passes:

```bash
find . -name "*.o" ! -newer kernel/rtlil.h | xargs rm -f
```

## Test

Test makefiles default `YOSYS=..\../yosys` (no `.exe`), which doesn't resolve under MSYS. Always invoke with the absolute `.exe` suffix:

```bash
YOSYS=../../yosys.exe make -j6 -C tests/various
```

**Canary tests** for hashlib/sigspec changes — these four catch fastmod / bucket-assignment bugs immediately:

```bash
YOSYS=../../yosys.exe make -j6 -C tests/various 2>&1 | \
  grep -E "^(PASS|FAIL) (wreduce|wreduce2|peepopt|muxpack)\.ys"
```

**Expected baseline failures (environmental, not regressions):**
| Directory | Failures | Cause |
|---|---|---|
| `tests/various` | 21 | abc/abc9 not built, no zlib, `/dev/null`, MSYS shell `mkdir` |
| `tests/opt` | 2 | abc-dependent (opt_lut, opt_hier) |
| `tests/verilog` | 4 | requires `sim` cmd (sim2 plugin) or `grep` shell |
| `tests/sat` | 2 | requires `sim` |
| `tests/techmap` | 16 | requires `abc` |
| `tests/fmt` | 13 | requires `iverilog` (Icarus Verilog) |

If anything else fails, it's likely your change.

## Repository layout

```
kernel/        Core data structures (RTLIL::*, hashlib, SigSpec, log, yosys_common)
frontends/     Verilog frontend (verilog/), AST handling (ast/), JSON, BLIF, etc.
passes/        Synthesis passes — biggest dirs are opt/ (~25 passes) and proc/
backends/      Output writers (verilog, blif, json, smt2, ...)
techlibs/      Tech-mapping libraries per FPGA family (xilinx, ice40, ecp5, ...)
libs/          Vendored deps (bigint, ezsat, json11, minisat, sha1)
tests/         Test suites — see "Test" above
benchmark-results/  Perf-loop scripts, synthetic benchmarks, historical numbers
agents/        Specialized agent playbooks (see below)
```

## Code style

- C++17, GNU dialect. Built with `-O3 -DNDEBUG`.
- Header includes group order: `kernel/yosys.h` first, then sibling headers, then `<system>`.
- Use `IdString` for symbol-table-y strings (interned). Use `std::string` for human-readable text.
- `log()` for normal output, `log_warning()` / `log_error()`. `log_assert()` for invariants (compiled out under `NDEBUG`).
- Pass interface: derive from `Pass`, register a global instance, implement `help()` + `execute()`. See `passes/opt/opt_expr.cc` for a worked example.
- Avoid `dict.reserve(N)` in mass-instantiated object ctors (e.g. `Cell::parameters`) — capacity reservation costs more than rehashing here. See `agents/perf-bisect.md` anti-patterns.

## Common one-liners

```bash
# Run a single Verilog source through synth flow
./yosys.exe -p "read_verilog file.v; synth; write_verilog out.v"

# Run a .ys script
./yosys.exe path/to/script.ys

# Time a benchmark
{ time ./yosys.exe -q benchmark-results/generated/picorv32_x4_synth.ys; } 2>&1 | grep real

# Quick bench across generated synthetic + picorv32 cases
bash benchmark-results/run_loop.sh <label>
```

## Working with multiple agents

Specialized playbooks live in `agents/`. When the user asks for work matching one of these, follow that playbook:

- [`agents/perf-bisect.md`](agents/perf-bisect.md) — performance-loop discipline (examine → hypothesize → edit → bench → test → commit). Used to produce ~1.85× geomean speedup. Encodes anti-patterns that previously broke the build, canary test list, and the per-Module generation-counter pattern that unlocked safe cross-execute() caches.

When adding a new agent playbook, add a one-line entry to the list above and put the file in `agents/`. Each playbook should be self-contained — list its inputs (what the user is asking for), its loop discipline, and its anti-patterns.

## Useful repo-specific docs

- `benchmark-results/PERF-WORK-SUMMARY.md` — cumulative log of optimization work (what landed, what didn't, why). Read before proposing a perf change to avoid retreading rejected ideas.
- `benchmark-results/SUMMARY-2026-04-24.md` — hashlib loops 6-10 detailed numbers.
- `agents/perf-bisect.md` — perf-loop playbook (see above).
- `README.md`, `CodingReadme` — upstream yosys docs (start here for the data model).

## Safety

- Don't push to `origin` without explicit user approval.
- Don't `--force` push to `main`; warn loudly if asked.
- Don't skip pre-commit hooks (`--no-verify`) — investigate hook failures.
- Never amend commits that have been pushed.
- Do not commit secrets, build artifacts (`*.exe`, `libyosys_exe.a`, `benchmark-results/*.json`), or generated test outputs (`tests/*/*.err`, `tests/*/*.log`).
