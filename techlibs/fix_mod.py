import sys
import subprocess
import re
import os

def main():
    script = sys.argv.pop(0)
    try:
        verilog, yosys = sys.argv
    except ValueError:
        print(f"Expected to be called as 'python3 {script} <cells_file> <yosys>'.")
        exit(1)

    proc = subprocess.run([yosys, '-p', f'read_verilog -lib {verilog}; write_verilog -blackboxes -'], stdout=subprocess.PIPE)
    modules = {}
    in_mod = False
    mod = ""
    decl = ""
    for line in proc.stdout.decode('utf-8').splitlines(keepends=True):
        m = re.match(r'(module (\S+)\(.+)', line, re.S)
        if m:
            decl, mod = m.groups()
            in_mod = True
        elif in_mod:
            decl += line
            
        if in_mod and decl.rstrip()[-1] == ';':
                in_mod = False
                modules[mod] = decl

    src = f'{verilog}.tmp'
    os.rename(verilog, src)
    dest = verilog

    with open(dest, 'w') as f_out:
        with open(src, 'r') as f_in:
            for line in f_in:
                m = re.match(r'module (\S+) \(\.\.\.\)', line)
                if m:
                    line = modules[m.group(1)]
                print(line, end='', file=f_out)

    if src.endswith('.tmp'):
        os.remove(src)

if __name__ == "__main__":
    main()
