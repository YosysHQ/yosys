#!/bin/bash

trap 'echo "ERROR in scratchpad.sh" >&2; exit 1' ERR

../../yosys -qp "scratchpad -set foo \"bar baz\"; \
scratchpad -copy foo oof; scratchpad -unset foo; \
tee -o scratchpad1.log scratchpad -get oof; \
tee -o scratchpad2.log scratchpad -get foo"

test "$(cat scratchpad1.log)" = "bar baz"
test "$(cat scratchpad2.log)" = "\"foo\" not set"

rm scratchpad1.log
rm scratchpad2.log
