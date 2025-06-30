
# 1. Initialize the submodules
git submodule update --init --recursive

# 2. Build the project
mkdir -p build
cmake -B build
cmake --build build --parallel $(nproc)

# 3. Install the project into test install dir
cmake --install build --prefix .

# 4. Test the project
# ctest -j$(nproc) --test-dir build --output-on-failure
# Or Rerun Failed Tests
# ctest -j$(nproc) --test-dir build --rerun-failed --output-on-failure
