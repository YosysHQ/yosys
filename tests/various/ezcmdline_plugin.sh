set -e

DIR=$(cd "$(dirname "$0")" && pwd)
BASEDIR=$(cd "$DIR/../.." && pwd)
rm -f "$DIR/ezcmdline_plugin.so"
chmod +x "$DIR/ezcmdline_dummy_solver"
"$BASEDIR/yosys-config" --build "$DIR/ezcmdline_plugin.so" "$DIR/ezcmdline_plugin.cc" -I"$BASEDIR"
"$BASEDIR/yosys" -m "$DIR/ezcmdline_plugin.so" -p "ezcmdline_test -cmd $DIR/ezcmdline_dummy_solver" | grep -q "ezcmdline_test passed!"
