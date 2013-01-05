#!/bin/bash
rm -rf rtl
svn co http://opencores.org/ocsvn/openrisc/openrisc/trunk/or1200/rtl/verilog rtl
( cd rtl; patch -p0 < ../config.patch; )
