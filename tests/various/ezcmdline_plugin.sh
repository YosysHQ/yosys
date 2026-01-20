set -e

DIR=$(cd "$(dirname "$0")" && pwd)
BASEDIR=$(cd "$DIR/../.." && pwd)
rm -f "$DIR/ezcmdline_plugin.so"
chmod +x "$DIR/ezcmdline_dummy_solver"
CXXFLAGS=$("$BASEDIR/yosys-config" --cxxflags)
DATDIR=$("$BASEDIR/yosys-config" --datdir)
DATDIR=${DATDIR//\//\\\/}
CXXFLAGS=${CXXFLAGS//$DATDIR/..\/..\/share}
"$BASEDIR/yosys-config" --exec --cxx ${CXXFLAGS} -I"$BASEDIR" --ldflags -shared -o "$DIR/ezcmdline_plugin.so" "$DIR/ezcmdline_plugin.cc"
"$BASEDIR/yosys" -m "$DIR/ezcmdline_plugin.so" -p "ezcmdline_test -cmd $DIR/ezcmdline_dummy_solver" | grep -q "ezcmdline_test passed!"
