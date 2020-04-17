set -e
rm -f plugin.so
CXXFLAGS=$(../../yosys-config --cxxflags)
CXXFLAGS=${CXXFLAGS// -I\/usr\/local\/share\/yosys\/include/ -I..\/..\/share\/include}
../../yosys-config --exec --cxx ${CXXFLAGS} --ldflags -shared -o plugin.so plugin.cc
../../yosys -m ./plugin.so -p "test" | grep -q "Plugin test passed!"
