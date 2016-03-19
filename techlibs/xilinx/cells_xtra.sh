#!/bin/bash

set -e
libdir="/opt/Xilinx/Vivado/2015.4/data/verilog/src"

function xtract_cell_decl()
{
	for dir in $libdir/xeclib $libdir/retarget; do
		[ -f $dir/$1.v ] || continue
		egrep '^\s*((end)?module|parameter|input|output|(end)?function|(end)?task)' $dir/$1.v |
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
	xtract_cell_decl BSCANE2
	# xtract_cell_decl BUFG
	xtract_cell_decl BUFGCE
	xtract_cell_decl BUFGCE_1
	xtract_cell_decl BUFGCTRL
	xtract_cell_decl BUFGMUX
	xtract_cell_decl BUFGMUX_1
	xtract_cell_decl BUFGMUX_CTRL
	xtract_cell_decl BUFH
	xtract_cell_decl BUFHCE
	xtract_cell_decl BUFIO
	xtract_cell_decl BUFMR
	xtract_cell_decl BUFMRCE
	xtract_cell_decl BUFR
	xtract_cell_decl CAPTUREE2
	# xtract_cell_decl CARRY4
	xtract_cell_decl CFGLUT5
	xtract_cell_decl DCIRESET
	xtract_cell_decl DNA_PORT
	xtract_cell_decl DSP48E1
	xtract_cell_decl EFUSE_USR
	# xtract_cell_decl FDCE
	# xtract_cell_decl FDPE
	# xtract_cell_decl FDRE
	# xtract_cell_decl FDSE
	xtract_cell_decl FIFO18E1
	xtract_cell_decl FIFO36E1
	xtract_cell_decl FRAME_ECCE2
	xtract_cell_decl GTHE2_CHANNEL
	xtract_cell_decl GTHE2_COMMON
	xtract_cell_decl GTPE2_CHANNEL
	xtract_cell_decl GTPE2_COMMON
	xtract_cell_decl GTXE2_CHANNEL
	xtract_cell_decl GTXE2_COMMON
	# xtract_cell_decl IBUF
	xtract_cell_decl IBUF_IBUFDISABLE
	xtract_cell_decl IBUF_INTERMDISABLE
	xtract_cell_decl IBUFDS
	xtract_cell_decl IBUFDS_DIFF_OUT
	xtract_cell_decl IBUFDS_DIFF_OUT_IBUFDISABLE
	xtract_cell_decl IBUFDS_DIFF_OUT_INTERMDISABLE
	xtract_cell_decl IBUFDS_GTE2
	xtract_cell_decl IBUFDS_IBUFDISABLE
	xtract_cell_decl IBUFDS_INTERMDISABLE
	xtract_cell_decl ICAPE2
	xtract_cell_decl IDDR
	xtract_cell_decl IDDR_2CLK
	xtract_cell_decl IDELAYCTRL
	xtract_cell_decl IDELAYE2
	xtract_cell_decl IN_FIFO
	xtract_cell_decl IOBUF
	xtract_cell_decl IOBUF_DCIEN
	xtract_cell_decl IOBUF_INTERMDISABLE
	xtract_cell_decl IOBUFDS
	xtract_cell_decl IOBUFDS_DCIEN
	xtract_cell_decl IOBUFDS_DIFF_OUT
	xtract_cell_decl IOBUFDS_DIFF_OUT_DCIEN
	xtract_cell_decl IOBUFDS_DIFF_OUT_INTERMDISABLE
	xtract_cell_decl ISERDESE2
	xtract_cell_decl KEEPER
	xtract_cell_decl LDCE
	xtract_cell_decl LDPE
	# xtract_cell_decl LUT1
	# xtract_cell_decl LUT2
	# xtract_cell_decl LUT3
	# xtract_cell_decl LUT4
	# xtract_cell_decl LUT5
	# xtract_cell_decl LUT6
	xtract_cell_decl LUT6_2
	xtract_cell_decl MMCME2_ADV
	xtract_cell_decl MMCME2_BASE
	# xtract_cell_decl MUXF7
	# xtract_cell_decl MUXF8
	# xtract_cell_decl OBUF
	xtract_cell_decl OBUFDS
	xtract_cell_decl OBUFT
	xtract_cell_decl OBUFTDS
	xtract_cell_decl ODDR
	xtract_cell_decl ODELAYE2
	xtract_cell_decl OSERDESE2
	xtract_cell_decl OUT_FIFO
	xtract_cell_decl PHASER_IN
	xtract_cell_decl PHASER_IN_PHY
	xtract_cell_decl PHASER_OUT
	xtract_cell_decl PHASER_OUT_PHY
	xtract_cell_decl PHASER_REF
	xtract_cell_decl PHY_CONTROL
	xtract_cell_decl PLLE2_ADV
	xtract_cell_decl PLLE2_BASE
	xtract_cell_decl PULLDOWN
	xtract_cell_decl PULLUP
	# xtract_cell_decl RAM128X1D
	xtract_cell_decl RAM128X1S
	xtract_cell_decl RAM256X1S
	xtract_cell_decl RAM32M
	xtract_cell_decl RAM32X1D
	xtract_cell_decl RAM32X1S
	xtract_cell_decl RAM32X1S_1
	xtract_cell_decl RAM32X2S
	xtract_cell_decl RAM64M
	# xtract_cell_decl RAM64X1D
	xtract_cell_decl RAM64X1S
	xtract_cell_decl RAM64X1S_1
	xtract_cell_decl RAM64X2S
	# xtract_cell_decl RAMB18E1
	# xtract_cell_decl RAMB36E1
	xtract_cell_decl ROM128X1
	xtract_cell_decl ROM256X1
	xtract_cell_decl ROM32X1
	xtract_cell_decl ROM64X1
	xtract_cell_decl SRL16E
	xtract_cell_decl SRLC32E
	xtract_cell_decl STARTUPE2
	xtract_cell_decl USR_ACCESSE2
	xtract_cell_decl XADC
} > cells_xtra.new

mv cells_xtra.new cells_xtra.v
exit 0

