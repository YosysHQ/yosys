#! /bin/bash

# Setup the CC / CXX from the matrix config
eval "${MATRIX_EVAL}"

# Look for location binaries first
export PATH="$HOME/.local-bin/bin:$PATH"

# OS X specific common setup
if [[ "$TRAVIS_OS_NAME" == "osx" ]]; then
	export PATH="/usr/local/opt/ccache/libexec:$PATH"
fi

# Parallel builds!
MAKEFLAGS="-j 2"
