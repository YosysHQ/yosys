#!/bin/bash

set -ex

XILINX_DIR=/opt/Xilinx/14.2/ISE_DS/ISE/

../../yosys - <<- EOT
	# read design
	read_verilog counter.v

	# high-level synthesis
	hierarchy -check -top counter
	proc; opt; fsm; opt; techmap; opt

	# mapping logic to LUTs using Berkeley ABC
	abc -lut 6; opt

	# map internal cells to FPGA cells
	techmap -map cells.v; opt

	# write netlist
	write_verilog -noattr testbench_synth.v
	write_edif testbench_synth.edif
EOT

iverilog -o testbench_gold counter_tb.v counter.v
iverilog -o testbench_gate counter_tb.v testbench_synth.v \
	$XILINX_DIR/verilog/src/{glbl,unisims/{FDRE,LUT1,LUT2,LUT3,LUT4,LUT5,LUT6}}.v

./testbench_gold > testbench_gold.txt
./testbench_gate > testbench_gate.txt

if diff -u testbench_gold.txt testbench_gate.txt; then
	set +x; echo; echo; banner "  PASS  "
else
	exit 1
fi

if [ "$*" = "-map" ]; then
	set -x

	cat > testbench_synth.ut <<- EOT
		-w
		-g DebugBitstream:No
		-g Binary:no
		-g CRC:Enable
		-g Reset_on_err:No
		-g ConfigRate:2
		-g ProgPin:PullUp
		-g TckPin:PullUp
		-g TdiPin:PullUp
		-g TdoPin:PullUp
		-g TmsPin:PullUp
		-g UnusedPin:PullDown
		-g UserID:0xFFFFFFFF
		-g ExtMasterCclk_en:No
		-g SPI_buswidth:1
		-g TIMER_CFG:0xFFFF
		-g multipin_wakeup:No
		-g StartUpClk:CClk
		-g DONE_cycle:4
		-g GTS_cycle:5
		-g GWE_cycle:6
		-g LCK_cycle:NoWait
		-g Security:None
		-g DonePipe:No
		-g DriveDone:No
		-g en_sw_gsr:No
		-g drive_awake:No
		-g sw_clk:Startupclk
		-g sw_gwe_cycle:5
		-g sw_gts_cycle:4
	EOT

	$XILINX_DIR/bin/lin64/edif2ngd testbench_synth.edif
	$XILINX_DIR/bin/lin64/ngdbuild -p xc7k70t testbench_synth
	$XILINX_DIR/bin/lin64/map -p xc7k70t-fbg676-1 -w -o testbench_mapped.ncd testbench_synth prffile.pcf
	$XILINX_DIR/bin/lin64/par -w testbench_mapped.ncd testbench_synth.ncd prffile.pcf
	$XILINX_DIR/bin/lin64/bitgen -f testbench_synth.ut testbench_synth.ncd
fi

if [ "$*" = "-clean" ]; then
	rm -rf netlist.lst _xmsgs/ prffile.pcf
	rm -f testbench_{synth,gold,gate,mapped}*
fi

