
import sys

with open(sys.argv[1], 'r') as f:
    rst = f.readlines()
    
new_rst = []
indent = ""
EoL = "\n"
code_start = f"::{EoL}{EoL}"
IsPreamble = True
WasDefinition = False
def_strip_count = 0
IsUsage = False
WasBlank = False
for line in rst:
    if line.isspace():
        # don't care about reformatting blank lines
        new_rst.append(line)
        WasBlank = True
    elif IsPreamble:
        # skip reformatting preamble
        new_rst.append(line)
        IsPreamble = '-'*80 not in line
    elif line.startswith(".. code-block::"):
        new_rst.append(f".. highlight:: none")
        IsUsage = True
    else:
        lstrip_count = len(line) - len(line.lstrip())
        stripped_line = line.strip()
        IsDefinition = stripped_line[0] == '-' and stripped_line[1] not in [' ','-']
        IsDedent = lstrip_count <= def_strip_count

        if IsUsage:
            # should be the first line of help output
            if stripped_line.startswith("See"):
                new_line = f"{stripped_line}{EoL}"
            else:
                new_line = f"Usage: :code:`{stripped_line}` {code_start}"
            IsUsage = False
        elif lstrip_count in [4,6,8] and IsDefinition and (WasBlank or WasDefinition):
            # format definition term
            new_line = f":code:`{stripped_line}` {code_start}"
            indent = "    "
            WasDefinition = True
            def_strip_count = lstrip_count
        elif WasDefinition and IsDedent:
            # no longer in definition, start new code block
            new_rst.append(code_start)
            new_line = line
            WasDefinition = False
        elif WasDefinition:
            # format definition
            new_line = f"{indent}{line[def_strip_count:]}"
        else:
            new_line = line
        
        new_rst.append(new_line)
        WasBlank = False
    
with open(sys.argv[1], 'w') as f:
    f.writelines(new_rst)
    
