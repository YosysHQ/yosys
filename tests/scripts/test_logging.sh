#!/usr/bin/env bash

var=0
rm -f quotes-*.log quotes-*.err

test_log()
{
    # Usage: test_log <log_str> <grep_str>
    var=$((var + 1))
    log_str="$1"
    grep_str="$2"
    log_file="quotes-$var.log"
    ../../yosys -QTq -l $log_file -p "log $log_str"
    if ! grep -qx "$grep_str" $log_file; then
        echo "ERROR: Expected 'yosys> log $log_str' to log '$grep_str'." > "quotes-$var.err"
        cat "quotes-$var.err"
    fi
}

test_log "test" "test"
test_log "test;" "test"
test_log "test;;" "test"
test_log "\"test" "\"test"
test_log "test\"" "test\""
test_log "\"test\"" "test"
test_log "\"test;\"" "test;"
test_log "\"test;;\"" "test;;"
test_log "\"test\" abc" "\"test\" abc"
test_log "\"#comments\" #123" "#comments"
test_log "\"!bang\"" "!bang"
test_log "\"spaces are cool too\"" "spaces are cool too"
test_log "\"log a\"; log b" "log a"
test_log "\"log a\"; log b" "b"
test_log "\"" "\""
test_log "\\\"" "\\\\\"" #\" == \"
test_log "\"abc\" \"def\"" "\"abc\" \"def\"" # don't abbreviate to abc" "def

errors=( quotes-*.err )
if [ -f $errors ] ; then
    exit 1
fi
