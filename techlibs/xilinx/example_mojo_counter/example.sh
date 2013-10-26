#!/bin/bash

set -ex

XILINX_DIR=/opt/Xilinx/14.5/ISE_DS/ISE/
XILINX_PART=xc6slx9-2-tqg144

../../../yosys - << EOT
# read design
read_verilog example.v

# high-level synthesis
hierarchy -check -top top
proc; opt; fsm; opt; techmap; opt

# mapping logic to LUTs using Berkeley ABC
abc -lut 6; opt

# map internal cells to FPGA cells
techmap -map ../cells.v; opt

# insert i/o buffers
iopadmap -outpad OBUF I:O -inpad BUFGP O:I

# write netlist
write_edif synth.edif
EOT

cat > bitgen.ut <<- EOT
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

$XILINX_DIR/bin/lin64/edif2ngd -a synth.edif synth.ngo
$XILINX_DIR/bin/lin64/ngdbuild -p $XILINX_PART -uc example.ucf synth.ngo synth.ngd
$XILINX_DIR/bin/lin64/map -p $XILINX_PART -w -o mapped.ncd synth.ngd constraints.pcf
$XILINX_DIR/bin/lin64/par -w mapped.ncd placed.ncd constraints.pcf
$XILINX_DIR/bin/lin64/bitgen -f bitgen.ut placed.ncd example.bit constraints.pcf

