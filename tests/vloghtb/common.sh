log_pass()
{
	printf "%-15s %s %s %s\n" "$1" "$2" "`printf "%20s" "$2" | tr -d a-zA-Z0-9_ | tr ' ' .`" "pass."
}

log_fail()
{
	printf "%-15s %s %s %s\n" "$1" "$2" "`printf "%20s" "$2" | tr -d a-zA-Z0-9_ | tr ' ' .`" "FAIL."
}

test_autotest()
{
	# Usage:
	# test_autotest <test_name> <mod_name> <vlog_file> <autotest_cmd_line_options>

	test_name="$1"
	mod_name="$2"
	vlog_file="$3"
	shift 3

	mkdir -p log_test_$test_name
	rm -rf log_test_$test_name/$mod_name.*

	cp $vlog_file log_test_$test_name/$mod_name.v

	cd log_test_$test_name
	if bash ../../tools/autotest.sh "$@" $mod_name.v > /dev/null 2>&1; then
		mv $mod_name.out $mod_name.txt
		log_pass test_$test_name $mod_name
	else
		log_fail test_$test_name $mod_name
	fi

	cd ..
}

test_equiv()
{
	# Usage:
	# test_equiv <test_name> <synth_script> <sat_options> <mod_name> <vlog_file>

	mkdir -p log_test_$1
	rm -f log_test_$1/$4.txt
	rm -f log_test_$1/$4.err

	if ! ../../yosys -q -l log_test_$1/$4.out - 2> /dev/null <<- EOT
		read_verilog $5
		proc;;

		copy $4 gold
		rename $4 work

		cd work
		$2
		cd ..

		miter -equiv -ignore_gold_x -make_outputs -make_outcmp gold work miter
		flatten miter
		sat $3 -verify -prove trigger 0 -show-inputs -show-outputs miter
	EOT
	then
		log_fail test_$1 $4
		mv log_test_$1/$4.out log_test_$1/$4.err
		exit 1
	fi

	log_pass test_$1 $4
	mv log_test_$1/$4.out log_test_$1/$4.txt
}
