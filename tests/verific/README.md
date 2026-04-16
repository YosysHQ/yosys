# Verific Test Cases

## Disabled

<!-- - `import_warning_operator`: no VHDL -->
<!-- - `mixed_flist`: no VHDL -->
- `memory_semantics`: relies on initial values being retained, which we do not want
- `rom_case`: we need different behavior for multi-port memories
- `blackbox*`: we need different behavior for parametrized blackboxes
- `chformal`: relies on initial values being retained, which we do not want
