#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")" && pwd)"
# Default to a Verific-enabled yosys; override with YOSYS env if needed.
YOSYS=${YOSYS:-"$ROOT/../../yosys-private/install/bin/yosys"}
# Default to the matching sby alongside the custom yosys; fall back to PATH.
SBY=${SBY:-"$ROOT/../../yosys-private/install/bin/sby"}
if [ ! -x "$SBY" ]; then
  SBY=sby
fi

tmpdir="$(mktemp -d "${TMPDIR:-/tmp}/yosys-staged-XXXX")"
trap 'rm -rf "$tmpdir"' EXIT

stage1_init="$tmpdir/stage_1_init.il"
stage1_fv="$tmpdir/stage_1_fv.il"
stage1_sby="$tmpdir/stage_1.sby"
stage1_dir="$tmpdir/stage_1"
witness="$stage1_dir/engine_0/trace0.yw"

stage2_init="$tmpdir/stage_2_init.il"
stage2_fv="$tmpdir/stage_2_fv.il"
stage2_sby="$tmpdir/stage_2.sby"
stage2_dir="$tmpdir/stage_2"

echo "Preparing staged formal witness replay test in $tmpdir"

# Convert the RTL once; both stages start from the same RTLIL.
"$YOSYS" -q -l "$tmpdir/convert.log" -p "
  verific -formal \"$ROOT/dut.sv\";
  verific -import -all;
  hierarchy -top dut;
  prep -top dut;
  flatten;
  write_rtlil \"$stage1_init\";
"

# Filter to phase 1 properties.
"$YOSYS" -q -l "$tmpdir/stage1_fv.log" -p "
  read_rtlil \"$stage1_init\";
  select */a:phase */a:phase=1 %d;
  delete;
  write_rtlil \"$stage1_fv\";
"

cat >"$stage1_sby" <<'EOF'
[options]
mode cover
depth 24

[engines]
smtbmc

[script]
read_rtlil stage_1_fv.il

[files]
stage_1_fv.il
EOF

(
  cd "$tmpdir"
  YOSYS="$YOSYS" "$SBY" -f "$stage1_sby"
)

if ! grep -qi "pass" "$stage1_dir/status"; then
  echo "stage 1 did not pass"
  cat "$stage1_dir/status" || true
  exit 1
fi

# Replay the witness into a new init-state IL for stage 2.
"$YOSYS" -q -l "$tmpdir/replay.log" -p "
  read_rtlil \"$stage1_init\";
  prep -top dut;
  sim -w -a -scope dut -r \"$witness\";
  write_rtlil \"$stage2_init\";
"

# Filter to phase 2 properties.
"$YOSYS" -q -l "$tmpdir/stage2_fv.log" -p "
  read_rtlil \"$stage2_init\";
  select */a:phase */a:phase=2 %d;
  delete;
  write_rtlil \"$stage2_fv\";
"

cat >"$stage2_sby" <<'EOF'
[options]
mode cover
depth 24

[engines]
smtbmc

[script]
read_rtlil stage_2_fv.il

[files]
stage_2_fv.il
EOF

(
  cd "$tmpdir"
  YOSYS="$YOSYS" "$SBY" -f "$stage2_sby"
)

if ! grep -qi "pass" "$stage2_dir/status"; then
  echo "stage 2 did not pass"
  cat "$stage2_dir/status" || true
  exit 1
fi

echo "Staged witness replay test passed."
