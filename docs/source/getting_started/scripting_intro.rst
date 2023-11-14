Scripting in Yosys
------------------

.. todo:: check logical consistency

Yosys reads and processes commands from synthesis scripts, command line
arguments and an interactive command prompt. Yosys commands consist of a command
name and an optional whitespace separated list of arguments. Commands are
terminated using the newline character or a semicolon (;). Empty lines and lines
starting with the hash sign (#) are ignored. See :ref:`sec:typusecase` for an
example synthesis script.

The command :cmd:ref:`help` can be used to access the command reference manual,
with ``help <command>`` providing details for a specific command.  ``yosys -H``
or ``yosys -h <command>`` will do the same outside of an interactive prompt.
The entire reference manual is also available here at :doc:`/cmd_ref`.

Example commands
~~~~~~~~~~~~~~~~

Commands for design navigation and investigation:

.. code-block:: yoscrypt

    cd                   # a shortcut for 'select -module <name>'
    ls                   # list modules or objects in modules
    dump                 # print parts of the design in RTLIL format
    show                 # generate schematics using graphviz
    select               # modify and view the list of selected objects

Commands for executing scripts or entering interactive mode:

.. code-block:: yoscrypt

    shell                # enter interactive command mode
    history              # show last interactive commands
    script               # execute commands from script file
    tcl                  # execute a TCL script file

Commands for reading and elaborating the design:

.. code-block:: yoscrypt

    read_rtlil           # read modules from RTLIL file
    read_verilog         # read modules from Verilog file
    hierarchy            # check, expand and clean up design hierarchy


Commands for high-level synthesis:

.. code-block:: yoscrypt

    proc                 # translate processes to netlists
    fsm                  # extract and optimize finite state machines
    memory               # translate memories to basic cells
    opt                  # perform simple optimizations


Commands for technology mapping:

.. code-block:: yoscrypt

    techmap              # generic technology mapper
    abc                  # use ABC for technology mapping
    dfflibmap            # technology mapping of flip-flops
    hilomap              # technology mapping of constant hi- and/or lo-drivers
    iopadmap             # technology mapping of i/o pads (or buffers)
    flatten              # flatten design

Commands for writing the results:

.. code-block:: yoscrypt

    write_blif           # write design to BLIF file
    write_btor           # write design to BTOR file
    write_edif           # write design to EDIF netlist file
    write_rtlil          # write design to RTLIL file
    write_spice          # write design to SPICE netlist file
    write_verilog        # write design to Verilog file


Script-Commands for standard synthesis tasks:

.. code-block:: yoscrypt

    synth                # generic synthesis script
    synth_xilinx         # synthesis for Xilinx FPGAs


Commands for model checking:

.. code-block:: yoscrypt

    sat                  # solve a SAT problem in the circuit
    miter                # automatically create a miter circuit
    scc                  # detect strongly connected components (logic loops)

Selections intro
~~~~~~~~~~~~~~~~

.. todo:: reorder text for logical consistency

Most commands can operate not only on the entire design but also specifically on
selected parts of the design. For example the command :cmd:ref:`dump` will print
all selected objects in the current design while ``dump foobar`` will only print
the module ``foobar`` and ``dump *`` will print the entire design regardless of
the current selection.

.. code:: yoscrypt

	dump */t:$add %x:+[A] */w:* %i

The selection mechanism is very powerful. For example the command above will
print all wires that are connected to the ``\A`` port of a ``$add`` cell.
Detailed documentation of the select framework can be found under
:doc:`/using_yosys/more_scripting/selections` or in the command reference at
:doc:`/cmd/select`.

The show command
~~~~~~~~~~~~~~~~

The :cmd:ref:`show` command requires a working installation of `GraphViz`_ and
`xdot`_ for generating the actual circuit diagrams.  Below is an example of how
this command can be used, showing the changes in the generated circuit at
different stages of the yosys tool flow.

.. _GraphViz: http://www.graphviz.org/

.. _xdot: https://github.com/jrfonseca/xdot.py

.. literalinclude:: /code_examples/show/example.ys
    :language: yoscrypt
    :caption: docs/source/code_examples/show/example.ys

.. literalinclude:: /code_examples/show/example.v
    :language: Verilog
    :caption: docs/source/code_examples/show/example.v

.. role:: yoscrypt(code)
   :language: yoscrypt

.. figure:: /_images/code_examples/show/example_00.*
   :class: width-helper
   
   ``example_00`` - shown after :yoscrypt:`read_verilog example.v`

.. figure:: /_images/code_examples/show/example_01.*
   :class: width-helper
   
   ``example_01`` - shown after :yoscrypt:`proc`

.. figure:: /_images/code_examples/show/example_02.*
   :class: width-helper
   
   ``example_02`` - shown after :yoscrypt:`opt`

A circuit diagram is generated for the design in its current state. Various
options can be used to change the appearance of the circuit diagram, set the
name and format for the output file, and so forth. When called without any
special options, it saves the circuit diagram in a temporary file and launches
``xdot`` to display the diagram. Subsequent calls to show re-use the ``xdot``
instance (if still running).

For more information on the :cmd:ref:`show` command, including a guide on what
the different symbols represent, see :ref:`interactive_show` and the 
:doc:`/using_yosys/more_scripting/interactive_investigation` page.
