#!/usr/bin/env python3

from __future__ import annotations
import fileinput
import json
from pathlib import Path

class SimHelper:
    name: str = ""
    title: str = ""
    ports: str = ""
    source: str = ""
    desc: list[str]
    code: list[str]
    ver: str = "1"

    def __init__(self) -> None:
        self.desc = []
    
    def __str__(self) -> str:
        printed_fields = [
            "name", "title", "ports", "source", "desc", "code", "ver",
        ]
        # generate C++ struct
        val = "tempCell = {\n"
        for field in printed_fields:
            field_val = getattr(self, field)
            if isinstance(field_val, list):
                field_val = "\n".join(field_val)
            val += f'  {json.dumps(field_val)},\n'
        val += "};\n"

        # map name to struct
        val += f'cell_help[{json.dumps(self.name)}] = tempCell;'
        val += "\n"
        val += f'cell_code[{json.dumps(self.name + "+")}] = tempCell;'
        return val

def simcells_reparse(cell: SimHelper):
    # cut manual signature
    cell.desc = cell.desc[3:]

    # code-block truth table
    new_desc = []
    indent = ""
    for line in cell.desc:
        if line.startswith("Truth table:"):
            indent = "   "
            new_desc.pop()
            new_desc.extend(["::", ""])
        new_desc.append(indent + line)
    cell.desc = new_desc

    # set version
    cell.ver = "2a"

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
        short_filename = Path(fileinput.filename()).name
        simHelper.source = f'{short_filename}:{fileinput.filelineno()}'
    elif not line.startswith("endmodule"):
        line = "    " + line
    try:
        simHelper.code.append(line.replace("\t", "    "))
    except AttributeError:
        # no module definition, ignore line
        pass
    if line.startswith("endmodule"):
        short_filename = Path(fileinput.filename()).name
        if simHelper.ver == "1" and short_filename == "simcells.v":
            # default simcells parsing
            simcells_reparse(simHelper)
        if not simHelper.desc:
            # no help
            simHelper.desc.append("No help message for this cell type found.\n")
        print(simHelper)
        simHelper = SimHelper()

