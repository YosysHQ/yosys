#!/usr/bin/env bash
pytest -v -m "not smt and not rkt" "$@"
