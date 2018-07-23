import sys
import os.path
sys.path.insert(0, os.path.dirname(__file__))

import gdb
import gdb.printing
import printers

gdb.printing.register_pretty_printer(
    gdb.current_objfile(),
    printers.build_pretty_printer())
