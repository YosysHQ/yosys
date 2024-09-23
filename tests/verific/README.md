# Verific Test Cases

## Yosys Built-In

### Working

- `case`
- `clocking`
- `enum`

### Skipped

- `bounds`: checks top and bottom bound attributes, which are removed to avoid OpenSTA issues
- `memory_semantics`: relies on initial values being retained, which we do not want
- `rom_case`: relies on using Verific's frontend rather than GHDL
