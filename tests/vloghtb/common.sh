log_pass()
{
	printf "%-15s %s %s %s\n" "$1" "$2" "`printf "%20s" "$2" | tr -d a-zA-Z0-9_ | tr ' ' .`" "pass."
}

log_fail()
{
	printf "%-15s %s %s %s\n" "$1" "$2" "`printf "%20s" "$2" | tr -d a-zA-Z0-9_ | tr ' ' .`" "FAIL."
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

		miter -equiv -flatten -ignore_gold_x -make_outputs -make_outcmp gold work miter
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
