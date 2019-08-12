#!/bin/bash

set -e
if [ -z "$1" ]
then
	libdir="/opt/Xilinx/Vivado/2018.1/data/verilog/src"
else
	libdir=$1
fi

function xtract_cell_decl()
{
	for dir in $libdir/xeclib $libdir/retarget; do
		[ -f $dir/$1.v ] || continue
		[ -z "$2" ] || echo $2
		egrep '^\s*((end)?module|parameter|input|inout|output|(end)?function|(end)?task)' $dir/$1.v |
			sed -re '/UNPLACED/ d; /^\s*function/,/endfunction/ d; /^\s*task/,/endtask/ d;
			         s,//.*,,; s/#?\(.*/(...);/; s/^(input|output|parameter)/ \1/;
			         s/\s+$//; s/,$/;/; /input|output|parameter/ s/[^;]$/&;/; s/\s+/ /g;
				 s/^ ((end)?module)/\1/; s/^ /    /; /module.*_bb/,/endmodule/ d;'
		echo; return
	done
	echo "Can't find $1."
	exit 1
}

{
	echo "// Created by cells_xtra.sh from Xilinx models"
	echo

	# Design elements types listed in Xilinx UG953
	xtract_cell_decl BSCANE2 "(* keep *)"
	# xtract_cell_decl BUFG "(* clkbuf_driver = \"O\" *)"
	xtract_cell_decl BUFGCE "(* clkbuf_driver = \"O\" *)"
	xtract_cell_decl BUFGCE_1 "(* clkbuf_driver = \"O\" *)"
	#xtract_cell_decl BUFGCTRL "(* clkbuf_driver = \"O\" *)"
	xtract_cell_decl BUFGMUX "(* clkbuf_driver = \"O\" *)"
	xtract_cell_decl BUFGMUX_1 "(* clkbuf_driver = \"O\" *)"
	xtract_cell_decl BUFGMUX_CTRL "(* clkbuf_driver = \"O\" *)"
	xtract_cell_decl BUFH "(* clkbuf_driver = \"O\" *)"
	#xtract_cell_decl BUFHCE "(* clkbuf_driver = \"O\" *)"
	xtract_cell_decl BUFIO "(* clkbuf_driver = \"O\" *)"
	xtract_cell_decl BUFMR "(* clkbuf_driver = \"O\" *)"
	xtract_cell_decl BUFMRCE "(* clkbuf_driver = \"O\" *)"
	xtract_cell_decl BUFR "(* clkbuf_driver = \"O\" *)"
	xtract_cell_decl CAPTUREE2 "(* keep *)"
	# xtract_cell_decl CARRY4
	xtract_cell_decl CFGLUT5 "(* clkbuf_sink = \"CLK\" *)"
	xtract_cell_decl DCIRESET "(* keep *)"
	xtract_cell_decl DNA_PORT
	xtract_cell_decl DSP48E1 "(* clkbuf_sink = \"CLK\" *)"
	xtract_cell_decl EFUSE_USR
	# xtract_cell_decl FDCE
	# xtract_cell_decl FDPE
	# xtract_cell_decl FDRE
	# xtract_cell_decl FDSE
	xtract_cell_decl FIFO18E1 "(* clkbuf_sink = \"RDCLK,WRCLK\" *)"
	xtract_cell_decl FIFO36E1 "(* clkbuf_sink = \"RDCLK,WRCLK\" *)"
	xtract_cell_decl FRAME_ECCE2
	xtract_cell_decl GTHE2_CHANNEL
	xtract_cell_decl GTHE2_COMMON
	xtract_cell_decl GTPE2_CHANNEL
	xtract_cell_decl GTPE2_COMMON
	xtract_cell_decl GTXE2_CHANNEL
	xtract_cell_decl GTXE2_COMMON
	# xtract_cell_decl IBUF "(* iopad_external_pin = \"I\" *)"
	xtract_cell_decl IBUF_IBUFDISABLE "(* iopad_external_pin = \"I\" *)"
	xtract_cell_decl IBUF_INTERMDISABLE "(* iopad_external_pin = \"I\" *)"
	xtract_cell_decl IBUFDS "(* iopad_external_pin = \"I,IB\" *)"
	xtract_cell_decl IBUFDS_DIFF_OUT "(* iopad_external_pin = \"I,IB\" *)"
	xtract_cell_decl IBUFDS_DIFF_OUT_IBUFDISABLE "(* iopad_external_pin = \"I,IB\" *)"
	xtract_cell_decl IBUFDS_DIFF_OUT_INTERMDISABLE "(* iopad_external_pin = \"I,IB\" *)"
	xtract_cell_decl IBUFDS_GTE2 "(* iopad_external_pin = \"I,IB\" *)"
	xtract_cell_decl IBUFDS_IBUFDISABLE "(* iopad_external_pin = \"I,IB\" *)"
	xtract_cell_decl IBUFDS_INTERMDISABLE "(* iopad_external_pin = \"I,IB\" *)"
	xtract_cell_decl IBUFG "(* iopad_external_pin = \"I\" *)"
	xtract_cell_decl IBUFGDS "(* iopad_external_pin = \"I,IB\" *)"
	xtract_cell_decl IBUFGDS_DIFF_OUT "(* iopad_external_pin = \"I,IB\" *)"
	xtract_cell_decl ICAPE2 "(* keep *)"
	xtract_cell_decl IDDR "(* clkbuf_sink = \"C\" *)"
	xtract_cell_decl IDDR_2CLK "(* clkbuf_sink = \"C,CB\" *)"
	xtract_cell_decl IDELAYCTRL "(* keep *) (* clkbuf_sink = \"REFCLK\" *)"
	xtract_cell_decl IDELAYE2 "(* clkbuf_sink = \"C\" *)"
	xtract_cell_decl IN_FIFO "(* clkbuf_sink = \"RDCLK,WRCLK\" *)"
	xtract_cell_decl IOBUF "(* iopad_external_pin = \"IO\" *)"
	xtract_cell_decl IOBUF_DCIEN "(* iopad_external_pin = \"IO\" *)"
	xtract_cell_decl IOBUF_INTERMDISABLE "(* iopad_external_pin = \"IO\" *)"
	xtract_cell_decl IOBUFDS "(* iopad_external_pin = \"IO\" *)"
	xtract_cell_decl IOBUFDS_DCIEN "(* iopad_external_pin = \"IO,IOB\" *)"
	xtract_cell_decl IOBUFDS_DIFF_OUT "(* iopad_external_pin = \"IO,IOB\" *)"
	xtract_cell_decl IOBUFDS_DIFF_OUT_DCIEN "(* iopad_external_pin = \"IO,IOB\" *)"
	xtract_cell_decl IOBUFDS_DIFF_OUT_INTERMDISABLE "(* iopad_external_pin = \"IO,IOB\" *)"
	xtract_cell_decl ISERDESE2 "(* clkbuf_sink = \"CLK,CLKB,CLKDIV,CLKDIVP,OCLK,OCLKB\" *)"
	xtract_cell_decl KEEPER
	xtract_cell_decl LDCE
	xtract_cell_decl LDPE
	# xtract_cell_decl LUT1
	# xtract_cell_decl LUT2
	# xtract_cell_decl LUT3
	# xtract_cell_decl LUT4
	# xtract_cell_decl LUT5
	# xtract_cell_decl LUT6
	#xtract_cell_decl LUT6_2
	xtract_cell_decl MMCME2_ADV
	xtract_cell_decl MMCME2_BASE
	# xtract_cell_decl MUXF7
	# xtract_cell_decl MUXF8
	# xtract_cell_decl OBUF "(* iopad_external_pin = \"O\" *)"
	xtract_cell_decl OBUFDS "(* iopad_external_pin = \"O,OB\" *)"
	xtract_cell_decl OBUFT "(* iopad_external_pin = \"O\" *)"
	xtract_cell_decl OBUFTDS "(* iopad_external_pin = \"O,OB\" *)"
	xtract_cell_decl ODDR "(* clkbuf_sink = \"C\" *)"
	xtract_cell_decl ODELAYE2 "(* clkbuf_sink = \"C\" *)"
	xtract_cell_decl OSERDESE2 "(* clkbuf_sink = \"CLK,CLKDIV\" *)"
	xtract_cell_decl OUT_FIFO "(* clkbuf_sink = \"RDCLK,WRCLK\" *)"
	xtract_cell_decl PHASER_IN
	xtract_cell_decl PHASER_IN_PHY
	xtract_cell_decl PHASER_OUT
	xtract_cell_decl PHASER_OUT_PHY
	xtract_cell_decl PHASER_REF
	xtract_cell_decl PHY_CONTROL
	xtract_cell_decl PLLE2_ADV
	xtract_cell_decl PLLE2_BASE
	xtract_cell_decl PS7 "(* keep *)"
	xtract_cell_decl PULLDOWN
	xtract_cell_decl PULLUP
	#xtract_cell_decl RAM128X1D "(* clkbuf_sink = \"WCLK\" *)"
	xtract_cell_decl RAM128X1S "(* clkbuf_sink = \"WCLK\" *)"
	xtract_cell_decl RAM256X1S "(* clkbuf_sink = \"WCLK\" *)"
	xtract_cell_decl RAM32M "(* clkbuf_sink = \"WCLK\" *)"
	#xtract_cell_decl RAM32X1D "(* clkbuf_sink = \"WCLK\" *)"
	xtract_cell_decl RAM32X1S "(* clkbuf_sink = \"WCLK\" *)"
	xtract_cell_decl RAM32X1S_1 "(* clkbuf_sink = \"WCLK\" *)"
	xtract_cell_decl RAM32X2S "(* clkbuf_sink = \"WCLK\" *)"
	xtract_cell_decl RAM64M "(* clkbuf_sink = \"WCLK\" *)"
	#xtract_cell_decl RAM64X1D "(* clkbuf_sink = \"WCLK\" *)"
	xtract_cell_decl RAM64X1S "(* clkbuf_sink = \"WCLK\" *)"
	xtract_cell_decl RAM64X1S_1 "(* clkbuf_sink = \"WCLK\" *)"
	xtract_cell_decl RAM64X2S "(* clkbuf_sink = \"WCLK\" *)"
	# xtract_cell_decl RAMB18E1 "(* clkbuf_sink = \"CLKARDCLK,CLKBWRCLK\" *)"
	# xtract_cell_decl RAMB36E1 "(* clkbuf_sink = \"CLKARDCLK,CLKBWRCLK\" *)"
	xtract_cell_decl ROM128X1
	xtract_cell_decl ROM256X1
	xtract_cell_decl ROM32X1
	xtract_cell_decl ROM64X1
	#xtract_cell_decl SRL16E "(* clkbuf_sink = \"CLK\" *)"
	#xtract_cell_decl SRLC32E "(* clkbuf_sink = \"CLK\" *)"
	xtract_cell_decl STARTUPE2 "(* keep *)"
	xtract_cell_decl USR_ACCESSE2
	xtract_cell_decl XADC
} > cells_xtra.new

mv cells_xtra.new cells_xtra.v
exit 0

