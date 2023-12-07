Loading a design
~~~~~~~~~~~~~~~~

keyword: Frontends

- :doc:`/cmd/read_verilog`

.. todo:: include ``read_verilog <<EOF``, also other methods of loading designs

.. code-block:: yoscrypt

    read_verilog file1.v
    read_verilog -I include_dir -D enable_foo -D WIDTH=12 file2.v
    read_verilog -lib cell_library.v

    verilog_defaults -add -I include_dir
    read_verilog file3.v
    read_verilog file4.v
    verilog_defaults -clear

    verilog_defaults -push
    verilog_defaults -add -I include_dir
    read_verilog file5.v
    read_verilog file6.v
    verilog_defaults -pop

.. todo:: more info on other ``read_*`` commands, also is this the first time we
   mention verific?

Others:

- :doc:`/cmd/read`
- `GHDL plugin`_ for VHDL
- :doc:`/cmd/read_rtlil` (direct textual representation of Yosys internal state)
- :doc:`/cmd/read_aiger`
- :doc:`/cmd/read_blif`
- :doc:`/cmd/read_json`
- :doc:`/cmd/read_liberty`

.. _GHDL plugin: https://github.com/ghdl/ghdl-yosys-plugin
