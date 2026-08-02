#!/usr/bin/env bash
set -e -x

# Build-time dependencies
## Linux Docker Images
if command -v yum &> /dev/null; then
    yum install -y flex # manylinux's bison versions are hopelessly out of date
fi

if command -v apk &> /dev/null; then
    apk add flex bison
fi

if ! printf '%s\n' '%require "3.8"' '%%' 'start: ;' | bison -o /dev/null /dev/stdin ; then
	(
		set -e -x
		cd bison
		./configure
		make clean
		make install -j$(getconf _NPROCESSORS_ONLN 2>/dev/null || sysctl -n hw.ncpu)
	)
fi

## macOS/Windows -- installed in GitHub Action itself, not container

# Runtime Dependencies
## Build Static FFI (platform-dependent but not Python version dependent)
(
	set -e -x
	cd ffi
	## Ultimate libyosys.so will be shared, so we need fPIC for the static libraries
	LDFLAGS=-fPIC CFLAGS=-fPIC CXXFLAGS=-fPIC ./configure --prefix=$PWD/pfx --enable-static --disable-shared
	make clean
	make install -j$(getconf _NPROCESSORS_ONLN 2>/dev/null || sysctl -n hw.ncpu)
)
