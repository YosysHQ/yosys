#!/bin/bash

# using Xilinx ISE to display RTL schematics

if [ ! -f "$1" ]; then
	echo "Usage: $0 <verilog-file>" >&2
	exit 1
fi

prjdir="$(dirname $0)/rtlview.tmp"
mkdir -p "$prjdir"

cp "$1" "$prjdir"/schematic.v
cp "$(dirname $0)"/../../techlibs/common/blackbox.v "$prjdir"/blackbox.v
cd "$prjdir"

if fuser -s ise.out; then
	echo "ISE already running. Re-create RTL schematic from GUI."
	exit 1
fi

xilver=$( ls -v /opt/Xilinx/ | grep '^[0-9]' | tail -n1; )

cat > rtlview.xise << EOT
<?xml version="1.0" encoding="UTF-8" standalone="no" ?>
<project xmlns="http://www.xilinx.com/XMLSchema" xmlns:xil_pn="http://www.xilinx.com/XMLSchema">
  <header/>
  <version xil_pn:ise_version="$xilver" xil_pn:schema_version="2"/>

  <files>
    <file xil_pn:name="schematic.v" xil_pn:type="FILE_VERILOG">
      <association xil_pn:name="BehavioralSimulation" xil_pn:seqID="1"/>
      <association xil_pn:name="Implementation" xil_pn:seqID="2"/>
    </file>
    <file xil_pn:name="blackbox.v" xil_pn:type="FILE_VERILOG">
      <association xil_pn:name="BehavioralSimulation" xil_pn:seqID="1"/>
      <association xil_pn:name="Implementation" xil_pn:seqID="2"/>
    </file>
  </files>

  <properties>
    <property xil_pn:name="Device" xil_pn:value="xc6slx4" xil_pn:valueState="default"/>
    <property xil_pn:name="Device Family" xil_pn:value="Spartan6" xil_pn:valueState="non-default"/>
    <property xil_pn:name="Device Speed Grade/Select ABS Minimum" xil_pn:value="-3" xil_pn:valueState="default"/>
  </properties>

  <bindings/>
  <libraries/>
  <autoManagedFiles/>
</project>
EOT

set --
case "$( uname -m )" in
x86_64)
	. /opt/Xilinx/$xilver/ISE_DS/settings64.sh ;;
*)
	. /opt/Xilinx/$xilver/ISE_DS/settings32.sh ;;
esac

ise rtlview.xise > ise.out 2>&1 &
echo "ISE is now starting up. Create RTL schematic from GUI."

