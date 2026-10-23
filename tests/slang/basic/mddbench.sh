#!/usr/bin/env sh
set -eu

cd "$(dirname "$0")/../mddbench"

uv sync --locked
cp config-slang-fails.yaml config.yaml

exec uv run python -m scripts.mau_runner -j 4 -k -f "$@"
