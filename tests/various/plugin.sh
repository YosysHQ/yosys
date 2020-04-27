set -e
rm -f plugin.so
CXXFLAGS=$(../../yosys-config --cxxflags)
DATDIR=$(../../yosys-config --datdir)
DATDIR=${DATDIR//\//\\\/}
CXXFLAGS=${CXXFLAGS//$DATDIR/..\/..\/share}
../../yosys-config --exec --cxx ${CXXFLAGS} --ldflags -shared -o plugin.so plugin.cc
../../yosys -m ./plugin.so -p "test" | grep -q "Plugin test passed!"
