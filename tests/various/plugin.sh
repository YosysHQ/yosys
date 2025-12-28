set -e
rm -f plugin.so
rm -rf plugin_search
CXXFLAGS=$(../../yosys-config --cxxflags)
DATDIR=$(../../yosys-config --datdir)
DATDIR=${DATDIR//\//\\\/}
CXXFLAGS=${CXXFLAGS//$DATDIR/..\/..\/share}
../../yosys-config --exec --cxx ${CXXFLAGS} --ldflags -shared -o plugin.so plugin.cc
../../yosys -m ./plugin.so -p "test" | grep -q "Plugin test passed!"
mkdir -p plugin_search
mv plugin.so plugin_search/plugin.so
YOSYS_PLUGIN_PATH=$PWD/plugin_search ../../yosys -m plugin.so -p "test" | grep -q "Plugin test passed!"
