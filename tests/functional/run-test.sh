#!/usr/bin/env bash
source ../common-env.sh

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )

pytest -v -m "not smt and not rkt" "$SCRIPT_DIR" "$@"
