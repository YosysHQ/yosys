Typical phases of a synthesis flow
----------------------------------

.. TODO: copypaste

- Reading and elaborating the design
- Higher-level synthesis and optimization

  - Converting ``always``-blocks to logic and registers
  - Perform coarse-grain optimizations (resource sharing, const folding, ...)
  - Handling of memories and other coarse-grain blocks
  - Extracting and optimizing finite state machines

- Convert remaining logic to bit-level logic functions
- Perform optimizations on bit-level logic functions
- Map bit-level logic gates and registers to cell library
- Write results to output file


Reading the design
~~~~~~~~~~~~~~~~~~

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


Design elaboration
~~~~~~~~~~~~~~~~~~

During design elaboration Yosys figures out how the modules are hierarchically
connected. It also re-runs the AST parts of the Verilog frontend to create all
needed variations of parametric modules.

.. code-block:: yoscrypt

    # simplest form. at least this version should be used after reading all input files
    #
    hierarchy

    # recommended form. fails if parts of the design hierarchy are missing, removes
    # everything that is unreachable from the top module, and marks the top module.
    #
    hierarchy -check -top top_module


The ``proc`` command
~~~~~~~~~~~~~~~~~~~~~~

The Verilog frontend converts ``always``-blocks to RTL netlists for the
expressions and "processess" for the control- and memory elements.

The ``proc`` command transforms this "processess" to netlists of RTL multiplexer
and register cells.

The ``proc`` command is actually a macro-command that calls the following other
commands:

.. code-block:: yoscrypt

    proc_clean      # remove empty branches and processes
    proc_rmdead     # remove unreachable branches
    proc_init       # special handling of "initial" blocks
    proc_arst       # identify modeling of async resets
    proc_mux        # convert decision trees to multiplexer networks
    proc_dff        # extract registers from processes
    proc_clean      # if all went fine, this should remove all the processes

Many commands can not operate on modules with "processess" in them. Usually a
call to ``proc`` is the first command in the actual synthesis procedure after
design elaboration.

Example
^^^^^^^

.. literalinclude:: ../../resources/PRESENTATION_ExSyn/proc_01.v
   :language: verilog
   :caption: ``docs/resources/PRESENTATION_ExSyn/proc_01.v``

.. literalinclude:: ../../resources/PRESENTATION_ExSyn/proc_01.ys
   :language: yoscrypt
   :caption: ``docs/resources/PRESENTATION_ExSyn/proc_01.ys``

.. figure:: ../../images/res/PRESENTATION_ExSyn/proc_01.*
    :class: width-helper

.. figure:: ../../images/res/PRESENTATION_ExSyn/proc_02.*
    :class: width-helper

.. literalinclude:: ../../resources/PRESENTATION_ExSyn/proc_02.v
   :language: verilog
   :caption: ``docs/resources/PRESENTATION_ExSyn/proc_02.v``

.. literalinclude:: ../../resources/PRESENTATION_ExSyn/proc_02.ys
   :language: yoscrypt
   :caption: ``docs/resources/PRESENTATION_ExSyn/proc_02.ys``

.. figure:: ../../images/res/PRESENTATION_ExSyn/proc_03.*
    :class: width-helper

.. literalinclude:: ../../resources/PRESENTATION_ExSyn/proc_03.ys
   :language: yoscrypt
   :caption: ``docs/resources/PRESENTATION_ExSyn/proc_03.ys``

.. literalinclude:: ../../resources/PRESENTATION_ExSyn/proc_03.v
   :language: verilog
   :caption: ``docs/resources/PRESENTATION_ExSyn/proc_03.v``


The ``opt`` command
~~~~~~~~~~~~~~~~~~~~~

The ``opt`` command implements a series of simple optimizations. It also is a
macro command that calls other commands:

.. code-block:: yoscrypt

    opt_expr                # const folding and simple expression rewriting
    opt_merge -nomux        # merging identical cells

    do
        opt_muxtree         # remove never-active branches from multiplexer tree
        opt_reduce          # consolidate trees of boolean ops to reduce functions
        opt_merge           # merging identical cells
        opt_rmdff           # remove/simplify registers with constant inputs
        opt_clean           # remove unused objects (cells, wires) from design
        opt_expr            # const folding and simple expression rewriting
    while [changed design]

The command ``clean`` can be used as alias for ``opt_clean``. And ``;;`` can be
used as shortcut for ``clean``. For example:

.. code-block:: yoscrypt

    proc; opt; memory; opt_expr;; fsm;;

Example
^^^^^^^

.. figure:: ../../images/res/PRESENTATION_ExSyn/opt_01.*
    :class: width-helper

.. literalinclude:: ../../resources/PRESENTATION_ExSyn/opt_01.ys
   :language: yoscrypt
   :caption: ``docs/resources/PRESENTATION_ExSyn/opt_01.ys``

.. literalinclude:: ../../resources/PRESENTATION_ExSyn/opt_01.v
   :language: verilog
   :caption: ``docs/resources/PRESENTATION_ExSyn/opt_01.v``

.. figure:: ../../images/res/PRESENTATION_ExSyn/opt_02.*
    :class: width-helper

.. literalinclude:: ../../resources/PRESENTATION_ExSyn/opt_02.ys
   :language: yoscrypt
   :caption: ``docs/resources/PRESENTATION_ExSyn/opt_02.ys``

.. literalinclude:: ../../resources/PRESENTATION_ExSyn/opt_02.v
   :language: verilog
   :caption: ``docs/resources/PRESENTATION_ExSyn/opt_02.v``

.. figure:: ../../images/res/PRESENTATION_ExSyn/opt_03.*
    :class: width-helper

.. literalinclude:: ../../resources/PRESENTATION_ExSyn/opt_03.ys
   :language: yoscrypt
   :caption: ``docs/resources/PRESENTATION_ExSyn/opt_03.ys``

.. literalinclude:: ../../resources/PRESENTATION_ExSyn/opt_03.v
   :language: verilog
   :caption: ``docs/resources/PRESENTATION_ExSyn/opt_03.v``

.. figure:: ../../images/res/PRESENTATION_ExSyn/opt_04.*
    :class: width-helper

.. literalinclude:: ../../resources/PRESENTATION_ExSyn/opt_04.v
   :language: verilog
   :caption: ``docs/resources/PRESENTATION_ExSyn/opt_04.v``

.. literalinclude:: ../../resources/PRESENTATION_ExSyn/opt_04.ys
   :language: yoscrypt
   :caption: ``docs/resources/PRESENTATION_ExSyn/opt_04.ys``


When to use ``opt`` or ``clean``
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Usually it does not hurt to call ``opt`` after each regular command in the
synthesis script. But it increases the synthesis time, so it is favourable to
only call ``opt`` when an improvement can be achieved.

The designs in ``yosys-bigsim`` are a good playground for experimenting with the
effects of calling ``opt`` in various places of the flow.

It generally is a good idea to call ``opt`` before inherently expensive commands
such as ``sat`` or ``freduce``, as the possible gain is much higher in this
cases as the possible loss.

The ``clean`` command on the other hand is very fast and many commands leave a
mess (dangling signal wires, etc). For example, most commands do not remove any
wires or cells. They just change the connections and depend on a later call to
clean to get rid of the now unused objects. So the occasional ``;;`` is a good
idea in every synthesis script.

The ``memory`` command
~~~~~~~~~~~~~~~~~~~~~~~~

In the RTL netlist, memory reads and writes are individual cells. This makes
consolidating the number of ports for a memory easier. The ``memory``
transforms memories to an implementation. Per default that is logic for address
decoders and registers. It also is a macro command that calls other commands:

.. code-block:: yoscrypt

    # this merges registers into the memory read- and write cells.
    memory_dff

    # this collects all read and write cells for a memory and transforms them
    # into one multi-port memory cell.
    memory_collect

    # this takes the multi-port memory cell and transforms it to address decoder
    # logic and registers. This step is skipped if "memory" is called with -nomap.
    memory_map

Usually it is preferred to use architecture-specific RAM resources for memory.
For example:

.. code-block:: yoscrypt

    memory -nomap; techmap -map my_memory_map.v; memory_map

Example
^^^^^^^

.. figure:: ../../images/res/PRESENTATION_ExSyn/memory_01.*
    :class: width-helper

.. literalinclude:: ../../resources/PRESENTATION_ExSyn/memory_01.ys
   :language: yoscrypt
   :caption: ``docs/resources/PRESENTATION_ExSyn/memory_01.ys``

.. literalinclude:: ../../resources/PRESENTATION_ExSyn/memory_01.v
   :language: verilog
   :caption: ``docs/resources/PRESENTATION_ExSyn/memory_01.v``

.. figure:: ../../images/res/PRESENTATION_ExSyn/memory_02.*
    :class: width-helper

.. literalinclude:: ../../resources/PRESENTATION_ExSyn/memory_02.v
   :language: verilog
   :caption: ``docs/resources/PRESENTATION_ExSyn/memory_02.v``

.. literalinclude:: ../../resources/PRESENTATION_ExSyn/memory_02.ys
   :language: yoscrypt
   :caption: ``docs/resources/PRESENTATION_ExSyn/memory_02.ys``


The ``fsm`` command
~~~~~~~~~~~~~~~~~~~~~

The ``fsm`` command identifies, extracts, optimizes (re-encodes), and
re-synthesizes finite state machines. It again is a macro that calls
a series of other commands:

.. code-block:: yoscrypt

    fsm_detect          # unless got option -nodetect
    fsm_extract

    fsm_opt
    clean
    fsm_opt

    fsm_expand          # if got option -expand
    clean               # if got option -expand
    fsm_opt             # if got option -expand

    fsm_recode          # unless got option -norecode

    fsm_info

    fsm_export          # if got option -export
    fsm_map             # unless got option -nomap

Some details on the most important commands from the ``fsm_*`` group:

The ``fsm_detect`` command identifies FSM state registers and marks them with
the ``(* fsm_encoding = "auto" *)`` attribute, if they do not have the
``fsm_encoding`` set already. Mark registers with ``(* fsm_encoding = "none"
*)`` to disable FSM optimization for a register.

The ``fsm_extract`` command replaces the entire FSM (logic and state registers)
with a ``$fsm`` cell.

The commands ``fsm_opt`` and ``fsm_recode`` can be used to optimize the FSM.

Finally the ``fsm_map`` command can be used to convert the (optimized) ``$fsm``
cell back to logic and registers.

The ``techmap`` command
~~~~~~~~~~~~~~~~~~~~~~~~~

.. figure:: ../../images/res/PRESENTATION_ExSyn/techmap_01.*
    :class: width-helper

The ``techmap`` command replaces cells with implementations given as
verilog source. For example implementing a 32 bit adder using 16 bit adders:

.. literalinclude:: ../../resources/PRESENTATION_ExSyn/techmap_01_map.v
   :language: verilog
   :caption: ``docs/resources/PRESENTATION_ExSyn/techmap_01_map.v``

.. literalinclude:: ../../resources/PRESENTATION_ExSyn/techmap_01.v
   :language: verilog
   :caption: ``docs/resources/PRESENTATION_ExSyn/techmap_01.v``

.. literalinclude:: ../../resources/PRESENTATION_ExSyn/techmap_01.ys
   :language: yoscrypt
   :caption: ``docs/resources/PRESENTATION_ExSyn/techmap_01.ys``

stdcell mapping
^^^^^^^^^^^^^^^

When ``techmap`` is used without a map file, it uses a built-in map file to map
all RTL cell types to a generic library of built-in logic gates and registers.

The built-in logic gate types are: ``$_NOT_``, ``$_AND_``, ``$_OR_``,
``$_XOR_``, and ``$_MUX_``.

The register types are: ``$_SR_NN_``, ``$_SR_NP_``, ``$_SR_PN_``, ``$_SR_PP_``,
``$_DFF_N_``, ``$_DFF_P_ $_DFF_NN0_``, ``$_DFF_NN1_``, ``$_DFF_NP0_``,
``$_DFF_NP1_``, ``$_DFF_PN0_``, ``$_DFF_PN1_``, ``$_DFF_PP0_ $_DFF_PP1_``,
``$_DFFSR_NNN_``, ``$_DFFSR_NNP_``, ``$_DFFSR_NPN_``, ``$_DFFSR_NPP_``,
``$_DFFSR_PNN_ $_DFFSR_PNP_``, ``$_DFFSR_PPN_``, ``$_DFFSR_PPP_``,
``$_DLATCH_N_``, and ``$_DLATCH_P_``.

See :doc:`/yosys_internals/formats/cell_library` for more about the internal
cells used.

The ``abc`` command
~~~~~~~~~~~~~~~~~~~~~

The ``abc`` command provides an interface to ABC_, an open source tool for
low-level logic synthesis.

.. _ABC: http://www.eecs.berkeley.edu/~alanmi/abc/

The ``abc`` command processes a netlist of internal gate types and can perform:

- logic minimization (optimization)
- mapping of logic to standard cell library (liberty format)
- mapping of logic to k-LUTs (for FPGA synthesis)

Optionally ``abc`` can process registers from one clock domain and perform
sequential optimization (such as register balancing).

ABC is also controlled using scripts. An ABC script can be specified to use more
advanced ABC features. It is also possible to write the design with
``write_blif`` and load the output file into ABC outside of Yosys.

Example
^^^^^^^

.. literalinclude:: ../../resources/PRESENTATION_ExSyn/abc_01.v
   :language: verilog
   :caption: ``docs/resources/PRESENTATION_ExSyn/abc_01.v``

.. literalinclude:: ../../resources/PRESENTATION_ExSyn/abc_01.ys
   :language: yoscrypt
   :caption: ``docs/resources/PRESENTATION_ExSyn/abc_01.ys``

.. figure:: ../../images/res/PRESENTATION_ExSyn/abc_01.*
    :class: width-helper

Other special-purpose mapping commands
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

``dfflibmap``
  This command maps the internal register cell types to the register types
  described in a liberty file.

``hilomap``
  Some architectures require special driver cells for driving a constant hi or
  lo value. This command replaces simple constants with instances of such driver
  cells.

``iopadmap``
  Top-level input/outputs must usually be implemented using special I/O-pad
  cells. This command inserts this cells to the design.

Example Synthesis Script
~~~~~~~~~~~~~~~~~~~~~~~~

.. code-block:: yoscrypt

    # read and elaborate design
    read_verilog cpu_top.v cpu_ctrl.v cpu_regs.v
    read_verilog -D WITH_MULT cpu_alu.v
    hierarchy -check -top cpu_top

    # high-level synthesis
    proc; opt; fsm;; memory -nomap; opt

    # substitute block rams
    techmap -map map_rams.v

    # map remaining memories
    memory_map

    # low-level synthesis
    techmap; opt; flatten;; abc -lut6
    techmap -map map_xl_cells.v

    # add clock buffers
    select -set xl_clocks t:FDRE %x:+FDRE[C] t:FDRE %d
    iopadmap -inpad BUFGP O:I @xl_clocks

    # add io buffers
    select -set xl_nonclocks w:* t:BUFGP %x:+BUFGP[I] %d
    iopadmap -outpad OBUF I:O -inpad IBUF O:I @xl_nonclocks

    # write synthesis results
    write_edif synth.edif

The weird ``select`` expressions at the end of this script are discussed later
in :doc:`using_yosys/more_scripting/selections</using_yosys/more_scripting/selections>`.
