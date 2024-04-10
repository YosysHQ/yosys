#!/usr/bin/env python3

from __future__ import annotations
import fileinput
import json

class SimHelper:
    name: str = ""
    title: str = ""
    ports: str = ""
    desc: list[str]
    code: list[str]
    ver: str = "1"

    def __init__(self) -> None:
        self.desc = []
    
    def __str__(self) -> str:
        val = "tempCell = {\n"
        val += f'  {json.dumps(self.name)},\n'
        val += f'  {json.dumps(self.title)},\n'
        val += f'  {json.dumps(self.ports)},\n'
        val += '  ' + json.dumps("\n".join(self.desc)) + ',\n'
        val += '  ' + json.dumps("\n".join(self.code)) + ',\n'
        val += f'  {json.dumps(self.ver)},\n'
        val += "};\n"
        val += f'cell_help[{json.dumps(self.name)}] = tempCell;'
        val += "\n"
        val += f'cell_code[{json.dumps(self.name + "+")}] = tempCell;'
        return val

simHelper = SimHelper()

for line in fileinput.input():
    line = line.rstrip()
    # special comments
    if line.startswith("//-"):
        simHelper.desc.append(line[4:] if len(line) > 4 else "")
    elif line.startswith("//* "):
        _, key, val = line.split(maxsplit=2)
        setattr(simHelper, key, val)
    
    # code parsing
    if line.startswith("module "):
        clean_line = line[7:].replace("\\", "").replace(";", "")
        simHelper.name, simHelper.ports = clean_line.split(maxsplit=1)
        simHelper.code = []
    elif not line.startswith("endmodule"):
        line = "    " + line
    try:
        simHelper.code.append(line.replace("\t", "    "))
    except AttributeError:
        # no module definition, ignore line
        pass
    if line.startswith("endmodule"):
        if not simHelper.desc:
            simHelper.desc.append("No help message for this cell type found.\n")
        print(simHelper)
        simHelper = SimHelper()

