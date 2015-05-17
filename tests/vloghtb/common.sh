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
	# test_autotest <test_name> <synth_script> <mod_name> <vlog_file>

	test_name="$1"
	synth_cmd="$2"
	mod_name="$3"
	vlog_file="$4"

	mkdir -p log_test_$test_name
	rm -rf log_test_$test_name/$mod_name.*

	../../yosys -q -l log_test_$test_name/$mod_name.out -o log_test_$test_name/$mod_name.v -p "$synth_cmd" "$vlog_file"
	cat spec/${mod_name}_spec.v scripts/check.v >> log_test_$test_name/$mod_name.v
	iverilog -o log_test_$test_name/$mod_name.bin -D"REFDAT_FN=\"refdat/${mod_name}_refdat.txt\"" log_test_$test_name/$mod_name.v

	if log_test_$test_name/$mod_name.bin 2>&1 | tee -a log_test_$test_name/$mod_name.out | grep -q '++OK++'; then
		mv log_test_$test_name/$mod_name.out log_test_$test_name/$mod_name.txt
		log_pass test_$test_name $mod_name
	else
		mv log_test_$test_name/$mod_name.out log_test_$test_name/$mod_name.err
		log_fail test_$test_name $mod_name
		exit 1
	fi
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

test_febe()
{
	# Usage:
	# test_febe <test_name> <synth_script> <extension> <backend> <frontend> <sat_options> <mod_name> <vlog_file>
	#           $1          $2             $3          $4        $5         $6            $7         $8

	mkdir -p log_test_$1
	rm -f log_test_$1/$7.txt
	rm -f log_test_$1/$7.err

	if ! ../../yosys -q -l log_test_$1/$7.out - 2> /dev/null <<- EOT
		echo on
		read_verilog $8
		$2
		design -save gold
		dump
		$4 log_test_$1/$7$3
		design -reset
		$5 log_test_$1/$7$3

		design -copy-from gold -as gold $7
		rename $7 gate

		miter -equiv -flatten -ignore_gold_x -make_outputs -make_outcmp gold gate miter
		sat $6 -verify -prove trigger 0 -show-inputs -show-outputs miter
	EOT
	then
		log_fail test_$1 $7
		mv log_test_$1/$7.out log_test_$1/$7.err
		exit 1
	fi

	log_pass test_$1 $7
	mv log_test_$1/$7.out log_test_$1/$7.txt
}
