Tests for the functional backend use pytest as a testrunner.

Run with `pytest -v`

Pytest options you might want:

- `-v`: More progress indication.

- `--basetemp tmp`: Store test files (including vcd results) in tmp. 
  CAREFUL: contents of tmp will be deleted

- `-k <pattern>`: Run only tests that contain the pattern, e.g.
  `-k cxx` or `-k smt` or `-k demux` or `-k 'cxx[demux`
 
- `-s`: Don't hide stdout/stderr from the test code.

Custom options for functional backend tests:

- `--per-cell N`: Run only N tests for each cell.
