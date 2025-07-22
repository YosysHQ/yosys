# Verific Test Cases

## Disabled

- `bounds`: relies on using Verific's VHDL frontend
- `memory_semantics`: relies on initial values being retained, which we do not want
- `rom_case`: relies on using Verific's VHDL frontend
- `blackbox*`: we need different behavior for parametrized blackboxes
- `chformal`: relies on initial values being retained, which we do not want
