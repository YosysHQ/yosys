#!/bin/sh

# This script builds the project using CMake in a way that is compatible with
# the existing Makefile build system.

# 1. Initialize the submodules
git submodule update --init --recursive

# 2. Build the project
mkdir -p build
cmake -B build -DCMAKE_BUILD_TYPE=Debug -D ENABLE_CCACHE:BOOL=ON -D CMAKE_INSTALL_PREFIX:PATH=/usr/local
cmake --build build --parallel $(nproc)

# 3. Install the project into test install dir
cmake --install build --prefix .

# 4. Test the project
# ctest -j$(nproc) --test-dir build --output-on-failure
# Or Rerun Failed Tests
# ctest -j$(nproc) --test-dir build --rerun-failed --output-on-failure
