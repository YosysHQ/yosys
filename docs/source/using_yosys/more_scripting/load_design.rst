Loading a design
----------------

.. _input files:

Input files on the command line
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

- guesses frontend based on file extension

  + ``.v`` -> ``read -vlog2k``
  + ``.sv`` -> ``read -sv``
  + ``.vhd`` and ``.vhdl`` -> ``read -vhdl``
  + ``.blif`` and ``.eblif`` -> `read_blif`
  + ``.json`` -> `read_json`
  + ``.il`` -> `read_rtlil` (direct textual representation of Yosys internal
    state)

- command line also supports

  + ``.ys`` -> `script`
  + ``.tcl`` -> `tcl`
  + ``-`` -> reads stdin and treats it as a script

The `read` command
~~~~~~~~~~~~~~~~~~

- standard method of loading designs
- also for defining macros and include directories
- uses `verific` command if available

  + ``-verific`` and ``-noverific`` options to enforce with/without Verific
  + check ``help read`` for more about the options available and the filetypes
    supported
  + elaborate designs with ``verific -import [options] <top>`` (or use
    `hierarchy`)

- fallback to `read_verilog` with ``-defer`` option

  + does not compile design until `hierarchy` command as discussed in
    :doc:`/getting_started/example_synth`
  + more similar to `verific` behaviour

- ``read -define`` et al mapped to `verific` or `verilog_defines`
- similarly, ``read -incdir`` et al mapped to `verific` or `verilog_defaults`

.. note::

   The Verific frontend for Yosys, which provides the :cmd:ref:`verific`
   command, requires Yosys to be built with Verific.  For full functionality,
   custom modifications to the Verific source code from YosysHQ are required,
   but limited useability can be achieved with some stock Verific builds.  Check
   :doc:`/yosys_internals/extending_yosys/build_verific` for more.

.. _Frontend:

Yosys frontends
~~~~~~~~~~~~~~~

- :doc:`/cmd/index_frontends`
- typically start with ``read_``
- built-in support for heredocs

  + in-line code with ``<<EOT``
  + can use any eot marker, but EOT (End-of-Transmission) and EOF
    (End-of-File) are most common

- built-in support for reading multiple files in the same command

  + executed as multiple successive calls to the frontend

- compatible with ``-f`` command line option, e.g. ``yosys -f verilog
  design.txt`` will use the `read_verilog` frontend with the input file
  ``design.txt``

- `verific` and `read` commands are technically not 'Frontends', but their
  behaviour is kept in sync

.. note::

   'Frontend' here means that the command is implemented as a sub-class of
   ``RTLIL::Frontend``, as opposed to the usual ``RTLIL::Pass``.

.. todo:: link note to as-yet non-existent section on ``RTLIL::Pass`` under 
          :doc:`/yosys_internals/extending_yosys/index`

The `read_verilog` command
""""""""""""""""""""""""""

- :cmd:title:`read_verilog`; also

  + :cmd:title:`verilog_defaults`,
  + :cmd:title:`verilog_defines`, and
  + :cmd:title:`read_verilog_file_list`

- supports most of Verilog-2005
- limited support for SystemVerilog
- some non-standard features/extensions for enabling formal verification
- please do not rely on `read_verilog` for syntax checking

  + recommend using a simulator (for example Icarus Verilog) or linting with
    another tool (such as verilator) first

.. todo:: figure out this example code block

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

Other built-in ``read_*`` commands
""""""""""""""""""""""""""""""""""

- :cmd:title:`read_rtlil`
- :cmd:title:`read_aiger`
- :cmd:title:`read_blif`
- :cmd:title:`read_json`
- :cmd:title:`read_liberty`
- :cmd:title:`read_xaiger2`

.. TODO:: does `write_file` count?

Externally maintained plugins
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

- `GHDL plugin`_ for VHDL (check ``help ghdl``)
- `yosys-slang plugin`_ for more comprehensive SystemVerilog support (check
  ``help read_slang``)

  + yosys-slang is implemented as a '`Frontend`_,' with all the built-in support
    that entails

.. _GHDL plugin: https://github.com/ghdl/ghdl-yosys-plugin
.. _yosys-slang plugin: https://github.com/povik/yosys-slang

- both plugins above are included in `OSS CAD Suite`_

.. _OSS CAD Suite: https://github.com/YosysHQ/oss-cad-suite-build

- `Synlig`_, which uses `Surelog`_ to provide SystemVerilog support

  + also implemented as a '`Frontend`_'

.. _Synlig: https://github.com/chipsalliance/synlig
.. _Surelog: https://github.com/chipsalliance/Surelog
