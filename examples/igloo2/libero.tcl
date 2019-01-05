# Run with "libero SCRIPT:libero.tcl"

new_project \
    -name top \
    -location work \
    -family IGLOO2 \
    -die PA4MGL500 \
    -package tq144 \
    -speed -1 \
    -hdl VERILOG

import_files -edif {example.edn}
run_tool –name {COMPILE}
run_tool –name {PLACEROUTEN}
