# Verific Test Cases

## Yosys Built-In

### Working

- `clocking`
- `enum`

### Skipped

- `bounds`: checks top and bottom bound attributes, which are removed to avoid OpenSTA issues
- `memory_semantics`: relies on initial values being retained, which is disabled
- `rom_case`: relies on using Verific's frontend rather than GHDL, which is what we are using

### Failing

- `case`: checks that miter works with abstract case synthesis, but runs into issues with function
