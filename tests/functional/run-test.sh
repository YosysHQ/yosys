#!/usr/bin/env bash
source ../common-env.sh
pytest -v -m "not smt and not rkt" "$@"
