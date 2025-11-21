#!/usr/bin/env bash

if ! timeout 5 ../../yosys bug5495.v -p 'hierarchy; techmap; abc -script bug5495.abc' ; then
    echo "Yosys failed to complete"
    exit 1
fi

