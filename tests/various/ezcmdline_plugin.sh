set -e

DIR=$(cd "$(dirname "$0")" && pwd)
BASEDIR=$(cd "$DIR/../.." && pwd)
rm -f "$DIR/ezcmdline_plugin.so"
chmod +x "$DIR/ezcmdline_dummy_solver"
CXXFLAGS=$(${YOSYS_CONFIG} --cxxflags)
DATDIR=$(${YOSYS_CONFIG} --datdir)
DATDIR=${DATDIR//\//\\\/}
CXXFLAGS=${CXXFLAGS//$DATDIR/$BUILD_DIR/share}
${YOSYS_CONFIG} --exec --cxx ${CXXFLAGS} -I"$BASEDIR" --ldflags -shared -o "$DIR/ezcmdline_plugin.so" "$DIR/ezcmdline_plugin.cc"
${YOSYS} -m "$DIR/ezcmdline_plugin.so" -p "ezcmdline_test -cmd $DIR/ezcmdline_dummy_solver" | grep -q "ezcmdline_test passed!"
