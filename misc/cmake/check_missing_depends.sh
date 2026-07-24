# Builds each Yosys component individually to make sure there aren't any missing static dependencies.
# Checking for dynamic dependencies would involve running the testsuite, which is much slower.

set -e
cmake .. -G Ninja -DCMAKE_CXX_COMPILER_LAUNCHER=ccache -DCMAKE_LINKER_TYPE=LLD
for comp in $(ninja --quiet print-yosys-components); do
	cmake . -DCOMPONENTS=$comp
	ninja --quiet yosys
done
