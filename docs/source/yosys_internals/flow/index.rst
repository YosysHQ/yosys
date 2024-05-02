Internal flow
=============

A (usually short) synthesis script controls Yosys.

These scripts contain three types of commands:

- **Frontends**, that read input files (usually Verilog);
- **Passes**, that perform transformations on the design in memory;
- **Backends**, that write the design in memory to a file (various formats are
  available: Verilog, BLIF, EDIF, SPICE, BTOR, . . .).

.. toctree:: 
	:maxdepth: 3

	overview
	control_and_data
	verilog_frontend

