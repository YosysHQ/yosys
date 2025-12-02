#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")" && pwd)"
YOSYS=${YOSYS:-"yosys"}
SBY=${SBY:-"sby"}

if [ -z "${OUTPUT_DIR:-}" ]; then
  tmpdir="$(mktemp -d "${TMPDIR:-/tmp}/yosys-staged-XXXX")"
  trap 'rm -rf "$tmpdir"' EXIT
else
  tmpdir="$OUTPUT_DIR"
  mkdir -p "$tmpdir"
  tmpdir="$(cd "$tmpdir" && pwd)"
fi

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

# Copy static assets into the temp dir.
cp "$ROOT"/{dut.sv,stage_1_init.ys,stage_1_fv.ys,stage_2_init.ys,stage_2_fv.ys,stage_1.sby,stage_2.sby} "$tmpdir"/

# Generate the initial IL for stage 1.
( cd "$tmpdir" && "$YOSYS" -q -l stage_1_init.log -s stage_1_init.ys )

# Filter to phase 1 properties to produce the final IL for stage 1, ready for
# formal verification.
( cd "$tmpdir" && "$YOSYS" -q -l stage1_fv.log -s stage_1_fv.ys )

# Run stage 1 formal verification to produce a witness.
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
( cd "$tmpdir" && "$YOSYS" -q -l stage_2_init.log -s stage_2_init.ys )

# Filter to phase 2 properties.
( cd "$tmpdir" && "$YOSYS" -q -l stage2_fv.log -s stage_2_fv.ys )

# Run stage 2 formal verification.
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
