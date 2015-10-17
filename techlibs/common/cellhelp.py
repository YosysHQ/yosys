#!/usr/bin/env python3

import fileinput
import json

current_help_msg = []
current_module_code = []
current_module_name = None
current_module_signature = None

def print_current_cell():
    print("cell_help[\"%s\"] = %s;" % (current_module_name, "\n".join([json.dumps(line) for line in current_help_msg])))
    print("cell_code[\"%s+\"] = %s;" % (current_module_name, "\n".join([json.dumps(line) for line in current_module_code])))

for line in fileinput.input():
    if line.startswith("//-"):
        current_help_msg.append(line[4:] if len(line) > 4 else "\n")
    if line.startswith("module "):
        current_module_name = line.split()[1].strip("\\")
        current_module_signature = " ".join(line.replace("\\", "").replace(";", "").split()[1:])
        current_module_code = []
    elif not line.startswith("endmodule"):
        line = "    " + line
    current_module_code.append(line.replace("\t", "    "))
    if line.startswith("endmodule"):
        if len(current_help_msg) == 0:
            current_help_msg.append("\n")
            current_help_msg.append("    %s\n" % current_module_signature)
            current_help_msg.append("\n")
            current_help_msg.append("No help message for this cell type found.\n")
            current_help_msg.append("\n")
        print_current_cell()
        current_help_msg = []

