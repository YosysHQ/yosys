yosys -import

proc read_stats { file } {
    set fid [open $file]
    set result [read $fid]
    close $fid
    set ports 0
    set nets 0
    foreach line [split $result "\n"] {
	if [regexp {Number of wires:[ \t]+([0-9]+)} $line tmp n] {
	    set nets [expr $nets + $n]
	}
	if [regexp {Number of ports:[ \t]+([0-9]+)} $line tmp n] {
	    set ports [expr $ports + $n]
	}
    }
    return [list $nets $ports]
}

proc assert_count { type actual expected } {
    if {$actual != $expected} {
	puts "Error, $type count: $actual vs $expected expected"
	exit 1
    }
}

read_verilog test_splitnets.v
hierarchy -auto-top
procs
design -save "pre"

splitnets -ports_only -top_only
write_verilog -noexpr "ports_only_in_top.v"
tee -o "ports_only_in_top.txt" stat
foreach {nets ports} [read_stats "ports_only_in_top.txt"] {}
assert_count "nets" $nets 26
assert_count "ports" $ports 16

design -load "pre"
splitnets -ports_only
write_verilog -noexpr "ports_only_in_all.v"
tee -o "ports_only_in_all.txt" stat
foreach {nets ports} [read_stats "ports_only_in_all.txt"] {}
assert_count "nets" $nets 30
assert_count "ports" $ports 20

design -load "pre"
splitnets -ports -top_only
write_verilog -noexpr "ports_nets_in_top.v"
tee -o "ports_nets_in_top.txt" stat
foreach {nets ports} [read_stats "ports_nets_in_top.txt"] {}
assert_count "nets" $nets 30
assert_count "ports" $ports 16

design -load "pre"
splitnets -ports
write_verilog -noexpr "ports_nets_in_all.v"
tee -o "ports_nets_in_all.txt" stat
foreach {nets ports} [read_stats "ports_nets_in_all.txt"] {}
assert_count "nets" $nets 40
assert_count "ports" $ports 20

exit 0
