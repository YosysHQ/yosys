log_pass() {
	printf "%-15s %s %s %s\n" "$1" "$2" "`printf "%20s" "$2" | tr -d a-zA-Z0-9_ | tr ' ' .`" "pass."
}

log_fail() {
	printf "%-15s %s %s %s\n" "$1" "$2" "`printf "%20s" "$2" | tr -d a-zA-Z0-9_ | tr ' ' .`" "FAIL."
}
