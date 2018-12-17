#!/usr/bin/env bash

set -e -x

if [ "$CONFIG" = "gcc" ]; then
	echo "Configuring for gcc."
	make config-gcc
elif [ "$CONFIG" = "clang" ]; then
	echo "Configuring for clang."
	make config-clang
else
    echo "CONFIG needs to be set to either 'clang' or 'gcc'" >&2
    exit 1
fi

make -j $(nproc)
