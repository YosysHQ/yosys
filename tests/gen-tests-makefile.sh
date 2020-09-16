set -eu

YOSYS_BASEDIR="$(cd "$(dirname "${BASH_SOURCE[0]}")"/../ >/dev/null 2>&1 && pwd)"

# $ generate_target target_name test_command
generate_target() {
	target_name=$1
	test_command=$2
	echo "all: $target_name"
	echo ".PHONY: $target_name"
	echo "$target_name:"
	printf "\t@%s\n" "$test_command"
	printf "\t@echo 'Passed %s'\n" "$target_name"
}

# $ generate_ys_test ys_file [yosys_args]
generate_ys_test() {
	ys_file=$1
	yosys_args=${2:-}
	generate_target "$ys_file" "$YOSYS_BASEDIR/yosys -ql ${ys_file%.*}.log $yosys_args $ys_file"
}

# $ generate_bash_test bash_file
generate_bash_test() {
	bash_file=$1
	generate_target "$bash_file" "bash -v $bash_file >${bash_file%.*}.log 2>&1"
}

# $ generate_tests [-y|--yosys-scripts] [-s|--prove-sv] [-b|--bash] [-a|--yosys-args yosys_args]
generate_tests() {
	do_ys=false
	do_sv=false
	do_sh=false
	yosys_args=""

	while [[ $# -gt 0 ]]; do
		arg="$1"
		case "$arg" in
			-y|--yosys-scripts)
				do_ys=true
				shift
				;;
			-s|--prove-sv)
				do_sv=true
				shift
				;;
			-b|--bash)
				do_sh=true
				shift
				;;
			-a|--yosys-args)
				yosys_args+="$2"
				shift
				shift
				;;
			*)
				echo >&2 "Unknown argument: $1"
				exit 1
		esac
	done

	if [[ ! ( $do_ys = true || $do_sv = true || $do_sh = true ) ]]; then
		echo >&2 "Error: No file types selected"
		exit 1
	fi

	echo ".PHONY: all"
	echo "all:"

	if [[ $do_ys = true ]]; then
		for x in *.ys; do
			generate_ys_test "$x" "$yosys_args"
		done
	fi;
	if [[ $do_sv = true ]]; then
		for x in *.sv; do
			if [ ! -f "${x%.sv}.ys"  ]; then
				generate_ys_test "$x" "-p \"prep -top top; sat -verify -prove-asserts\" $yosys_args"
			fi;
		done
	fi;
	if [[ $do_sh == true ]]; then
		for s in *.sh; do
			if [ "$s" != "run-test.sh" ]; then
				generate_bash_test "$s"
			fi
		done
	fi
}

run_tests() {
	generate_tests "$@" > run-test.mk
	exec ${MAKE:-make} -f run-test.mk
}
