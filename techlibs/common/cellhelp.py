#!/usr/bin/env python3

import fileinput
import json

current_help_msg = []
current_module_code = []
current_module_name = None

def print_current_cell():
    print("cell_help[\"%s\"] = %s;" % (current_module_name, "\n".join([json.dumps(line) for line in current_help_msg])))
    print("cell_code[\"%s+\"] = %s;" % (current_module_name, "\n".join([json.dumps(line) for line in current_module_code])))

for line in fileinput.input():
    if line.startswith("//-"):
        current_help_msg.append(line[4:] if len(line) > 4 else "\n")
    if line.startswith("module "):
        current_module_name = line.split()[1].strip("\\")
        current_module_code = []
    current_module_code.append(line)
    if line.startswith("endmodule"):
        if len(current_help_msg) > 0:
            print_current_cell()
        current_help_msg = []

