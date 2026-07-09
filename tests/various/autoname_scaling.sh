#!/usr/bin/env bash
# Regression test for the incremental worklist rewrite of autoname_worker
# ("autoname: avoid O(iterations x module size) full rescan").
#
# Before that change, AutonamePass::execute() rescanned every selected
# cell's every connection on every round. Naming only propagates one hop
# per round, so a design containing a long public-name-to-public-name
# propagation chain of length N needed O(N) rounds, each doing an O(N)
# rescan: O(N^2) total. This builds such a chain and checks that autoname
# finishes within a time budget the old O(N^2) algorithm could not meet
# (it took tens of seconds at this size; the fixed algorithm takes low
# single-digit seconds), without pinning an exact runtime, which would be
# too flaky across machines.

set -e

if ! which timeout > /dev/null; then
    echo "No 'timeout', skipping test"
    exit 0
fi

n=10000
il=autoname_scaling.il
trap 'rm -f $il' EXIT

{
    echo 'module \top'
    echo '  wire input 1 \a'
    for i in $(seq 0 $((n-1))); do
        echo "  wire \$w$i"
    done
    prev='\a'
    for i in $(seq 0 $((n-1))); do
        echo "  cell \$not \$c$i"
        echo '    parameter \A_SIGNED 0'
        echo '    parameter \A_WIDTH 1'
        echo '    parameter \Y_WIDTH 1'
        echo "    connect \\A $prev"
        echo "    connect \\Y \$w$i"
        echo '  end'
        prev="\$w$i"
    done
    echo 'end'
} > $il

if ! timeout 20 ${YOSYS} -q -p "read_rtlil $il; autoname" ; then
    echo "autoname did not finish a $n-long propagation chain within the time" \
         "budget -- looks like the O(iterations x module size) full-rescan" \
         "behaviour is back"
    exit 1
fi
