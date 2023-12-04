Typical phases of a synthesis flow
----------------------------------

.. role:: yoscrypt(code)
   :language: yoscrypt

.. todo:: should e.g. :yoscrypt:`proc` and :yoscrypt:`memory` examples be 
   included here (typical phases) or examples

.. todo:: expand bullet points

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

.. todo:: include ``read_verilog <<EOF`` when discussing how to read designs?

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

.. todo:: hierarchy without ``-top`` is bad
   - resolve non-module-specific references (sub modules, interfaces et al)
   - check sub modules exist, discarding unused
   - set top attribute
   - also mention failure modes
   - also prep?

.. code-block:: yoscrypt

    # simplest form. at least this version should be used after reading all input files
    #
    hierarchy

    # recommended form. fails if parts of the design hierarchy are missing, removes
    # everything that is unreachable from the top module, and marks the top module.
    #
    hierarchy -check -top top_module


Converting process blocks
~~~~~~~~~~~~~~~~~~~~~~~~~

The Verilog frontend converts ``always``-blocks to RTL netlists for the
expressions and "processess" for the control- and memory elements. The
:cmd:ref:`proc` command then transforms these "processess" to netlists of RTL
multiplexer and register cells. It also is a macro command that calls the other
``proc_*`` commands in a sensible order:

#. :cmd:ref:`proc_clean` removes empty branches and processes.
#. :cmd:ref:`proc_rmdead` removes unreachable branches.
#. :cmd:ref:`proc_prune`
#. :cmd:ref:`proc_init` special handling of "initial" blocks.
#. :cmd:ref:`proc_arst` identifies modeling of async resets.
#. :cmd:ref:`proc_rom`
#. :cmd:ref:`proc_mux` converts decision trees to multiplexer networks.
#. :cmd:ref:`proc_dlatch`
#. :cmd:ref:`proc_dff` extracts registers from processes.
#. :cmd:ref:`proc_memwr`
#. :cmd:ref:`proc_clean` this should remove all the processes, provided all went
   fine.

After all the ``proc_*`` commands, :yoscrypt:`opt_expr` is called. This can be
disabled by calling :yoscrypt:`proc -noopt`.  For more information about
:cmd:ref:`proc`, such as disabling certain sub commands, see :doc:`/cmd/proc`.

Many commands can not operate on modules with "processess" in them. Usually a
call to :cmd:ref:`proc` is the first command in the actual synthesis procedure
after design elaboration.

Example
^^^^^^^

.. todo:: describe ``proc`` images

.. literalinclude:: /code_examples/synth_flow/proc_01.v
   :language: verilog
   :caption: ``docs/source/code_examples/synth_flow/proc_01.v``

.. literalinclude:: /code_examples/synth_flow/proc_01.ys
   :language: yoscrypt
   :caption: ``docs/source/code_examples/synth_flow/proc_01.ys``

.. figure:: /_images/code_examples/synth_flow/proc_01.*
   :class: width-helper

.. figure:: /_images/code_examples/synth_flow/proc_02.*
   :class: width-helper

.. literalinclude:: /code_examples/synth_flow/proc_02.v
   :language: verilog
   :caption: ``docs/source/code_examples/synth_flow/proc_02.v``

.. literalinclude:: /code_examples/synth_flow/proc_02.ys
   :language: yoscrypt
   :caption: ``docs/source/code_examples/synth_flow/proc_02.ys``

.. figure:: /_images/code_examples/synth_flow/proc_03.*
   :class: width-helper

.. literalinclude:: /code_examples/synth_flow/proc_03.ys
   :language: yoscrypt
   :caption: ``docs/source/code_examples/synth_flow/proc_03.ys``

.. literalinclude:: /code_examples/synth_flow/proc_03.v
   :language: verilog
   :caption: ``docs/source/code_examples/synth_flow/proc_03.v``


Optimizations
~~~~~~~~~~~~~

The :cmd:ref:`opt` command implements a series of simple optimizations. It also
is a macro command that calls other commands:

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

The command :cmd:ref:`clean` can be used as alias for :cmd:ref:`opt_clean`. And
``;;`` can be used as shortcut for :cmd:ref:`clean`. For example:

.. code-block:: yoscrypt

    hierarchy; proc; opt; memory; opt_expr;; fsm;;

Example
"""""""

.. todo:: describe ``opt`` images

.. figure:: /_images/code_examples/synth_flow/opt_01.*
   :class: width-helper

.. literalinclude:: /code_examples/synth_flow/opt_01.ys
   :language: yoscrypt
   :caption: ``docs/source/code_examples/synth_flow/opt_01.ys``

.. literalinclude:: /code_examples/synth_flow/opt_01.v
   :language: verilog
   :caption: ``docs/source/code_examples/synth_flow/opt_01.v``

.. figure:: /_images/code_examples/synth_flow/opt_02.*
   :class: width-helper

.. literalinclude:: /code_examples/synth_flow/opt_02.ys
   :language: yoscrypt
   :caption: ``docs/source/code_examples/synth_flow/opt_02.ys``

.. literalinclude:: /code_examples/synth_flow/opt_02.v
   :language: verilog
   :caption: ``docs/source/code_examples/synth_flow/opt_02.v``

.. figure:: /_images/code_examples/synth_flow/opt_03.*
   :class: width-helper

.. literalinclude:: /code_examples/synth_flow/opt_03.ys
   :language: yoscrypt
   :caption: ``docs/source/code_examples/synth_flow/opt_03.ys``

.. literalinclude:: /code_examples/synth_flow/opt_03.v
   :language: verilog
   :caption: ``docs/source/code_examples/synth_flow/opt_03.v``

.. figure:: /_images/code_examples/synth_flow/opt_04.*
   :class: width-helper

.. literalinclude:: /code_examples/synth_flow/opt_04.v
   :language: verilog
   :caption: ``docs/source/code_examples/synth_flow/opt_04.v``

.. literalinclude:: /code_examples/synth_flow/opt_04.ys
   :language: yoscrypt
   :caption: ``docs/source/code_examples/synth_flow/opt_04.ys``

When to use :cmd:ref:`opt` or :cmd:ref:`clean`
""""""""""""""""""""""""""""""""""""""""""""""

Usually it does not hurt to call :cmd:ref:`opt` after each regular command in
the synthesis script. But it increases the synthesis time, so it is favourable
to only call :cmd:ref:`opt` when an improvement can be achieved.

It is generally a good idea to call :cmd:ref:`opt` before inherently expensive
commands such as :cmd:ref:`sat` or :cmd:ref:`freduce`, as the possible gain is
much higher in these cases as the possible loss.

The :cmd:ref:`clean` command on the other hand is very fast and many commands
leave a mess (dangling signal wires, etc). For example, most commands do not
remove any wires or cells. They just change the connections and depend on a
later call to clean to get rid of the now unused objects. So the occasional
``;;`` is a good idea in every synthesis script.

Other common optimization commands
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. todo:: fill out descriptions for other optimization commands

:cmd:ref:`wreduce`
    Reduces the word size of operations.

:cmd:ref:`peepopt`
    Applies a collection of peephole optimizers to the current design.

:cmd:ref:`share`
    Merges shareable resources into a single resource using a SAT solver to
    determine if two resources are shareable.

Memory handling
~~~~~~~~~~~~~~~

In the RTL netlist, memory reads and writes are individual cells. This makes
consolidating the number of ports for a memory easier. The :cmd:ref:`memory`
transforms memories to an implementation. Per default that is logic for address
decoders and registers. It also is a macro command that calls the other
``memory_*`` commands in a sensible order:

.. todo:: fill out missing :cmd:ref:`memory` subcommands descriptions

#. :cmd:ref:`memory_bmux2rom`
#. :cmd:ref:`memory_dff` merges registers into the memory read- and write cells.
#. :cmd:ref:`memory_share`
#. :cmd:ref:`memory_memx`
#. :cmd:ref:`memory_collect` collects all read and write cells for a memory and
   transforms them into one multi-port memory cell.
#. :cmd:ref:`memory_bram`
#. :cmd:ref:`memory_map` takes the multi-port memory cell and transforms it to
   address decoder logic and registers.

.. todo:: is :yoscrypt:`memory -nomap; techmap -map my_memory_map.v; memory_map`
   superceded by :yoscrypt:`memory_libmap`?

Usually it is preferred to use architecture-specific RAM resources for memory.
For example:

.. code-block:: yoscrypt

    memory -nomap; techmap -map my_memory_map.v; memory_map

For more information about :cmd:ref:`memory`, such as disabling certain sub
commands, see :doc:`/cmd/memory`.

Example
^^^^^^^

.. todo:: describe ``memory`` images

.. figure:: /_images/code_examples/synth_flow/memory_01.*
   :class: width-helper

.. literalinclude:: /code_examples/synth_flow/memory_01.ys
   :language: yoscrypt
   :caption: ``docs/source/code_examples/synth_flow/memory_01.ys``

.. literalinclude:: /code_examples/synth_flow/memory_01.v
   :language: verilog
   :caption: ``docs/source/code_examples/synth_flow/memory_01.v``

.. figure:: /_images/code_examples/synth_flow/memory_02.*
   :class: width-helper

.. literalinclude:: /code_examples/synth_flow/memory_02.v
   :language: verilog
   :caption: ``docs/source/code_examples/synth_flow/memory_02.v``

.. literalinclude:: /code_examples/synth_flow/memory_02.ys
   :language: yoscrypt
   :caption: ``docs/source/code_examples/synth_flow/memory_02.ys``

The :cmd:ref:`memory_libmap` command
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. todo:: :cmd:ref:`memory_libmap` description

FSM handling
~~~~~~~~~~~~

The :cmd:ref:`fsm` command identifies, extracts, optimizes (re-encodes), and
re-synthesizes finite state machines. It again is a macro that calls a series of
other commands:

#. :cmd:ref:`fsm_detect` identifies FSM state registers and marks them
   with the ``(* fsm_encoding = "auto" *)`` attribute, if they do not have the
   ``fsm_encoding`` set already. Mark registers with ``(* fsm_encoding = "none"
   *)`` to disable FSM optimization for a register.
#. :cmd:ref:`fsm_extract` replaces the entire FSM (logic and state registers)
   with a ``$fsm`` cell.
#. :cmd:ref:`fsm_opt` optimizes the FSM. Called multiple times.
#. :cmd:ref:`fsm_expand` optionally merges additional auxilliary gates into the
   ``$fsm`` cell.
#. :cmd:ref:`fsm_recode` also optimizes the FSM.
#. :cmd:ref:`fsm_info` logs internal FSM information.
#. :cmd:ref:`fsm_export` optionally exports each FSM to KISS2 files.
#. :cmd:ref:`fsm_map` converts the (optimized) ``$fsm`` cell back to logic and
   registers.

See also :doc:`/cmd/fsm`.

DSP handling
~~~~~~~~~~~~

.. todo:: add info about dsp handling

Technology mapping
~~~~~~~~~~~~~~~~~~

The :cmd:ref:`techmap` command replaces cells with implementations given as
verilog source. For example implementing a 32 bit adder using 16 bit adders:

.. figure:: /_images/code_examples/synth_flow/techmap_01.*
   :class: width-helper

.. literalinclude:: /code_examples/synth_flow/techmap_01_map.v
   :language: verilog
   :caption: ``docs/source/code_examples/synth_flow/techmap_01_map.v``

.. literalinclude:: /code_examples/synth_flow/techmap_01.v
   :language: verilog
   :caption: ``docs/source/code_examples/synth_flow/techmap_01.v``

.. literalinclude:: /code_examples/synth_flow/techmap_01.ys
   :language: yoscrypt
   :caption: ``docs/source/code_examples/synth_flow/techmap_01.ys``

See :doc:`/yosys_internals/techmap` for more.

stdcell mapping
^^^^^^^^^^^^^^^

When :cmd:ref:`techmap` is used without a map file, it uses a built-in map file
to map all RTL cell types to a generic library of built-in logic gates and
registers.

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

The :cmd:ref:`abc` command
~~~~~~~~~~~~~~~~~~~~~~~~~~

The :cmd:ref:`abc` command provides an interface to ABC_, an open source tool
for low-level logic synthesis.

.. _ABC: http://www.eecs.berkeley.edu/~alanmi/abc/

The :cmd:ref:`abc` command processes a netlist of internal gate types and can
perform:

- logic minimization (optimization)
- mapping of logic to standard cell library (liberty format)
- mapping of logic to k-LUTs (for FPGA synthesis)

Optionally :cmd:ref:`abc` can process registers from one clock domain and
perform sequential optimization (such as register balancing).

ABC is also controlled using scripts. An ABC script can be specified to use more
advanced ABC features. It is also possible to write the design with
:cmd:ref:`write_blif` and load the output file into ABC outside of Yosys.

Example
^^^^^^^

.. todo:: describe ``abc`` images

.. literalinclude:: /code_examples/synth_flow/abc_01.v
   :language: verilog
   :caption: ``docs/source/code_examples/synth_flow/abc_01.v``

.. literalinclude:: /code_examples/synth_flow/abc_01.ys
   :language: yoscrypt
   :caption: ``docs/source/code_examples/synth_flow/abc_01.ys``

.. figure:: /_images/code_examples/synth_flow/abc_01.*
   :class: width-helper

Other special-purpose mapping commands
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The commands below may be used depending on the targeted architecture for
compatibility with, or to take advantage of, resources available.

:cmd:ref:`dfflibmap`
    This command maps the internal register cell types to the register types
    described in a liberty file.

:cmd:ref:`hilomap`
    Some architectures require special driver cells for driving a constant hi or
    lo value. This command replaces simple constants with instances of such
    driver cells.

:cmd:ref:`iopadmap`
    Top-level input/outputs must usually be implemented using special I/O-pad
    cells. This command inserts such cells to the design.

:cmd:ref:`alumacc`
    Translate arithmetic operations like $add, $mul, $lt, etc. to $alu and $macc
    cells.

:cmd:ref:`dfflegalize`
    Specify a set of supported FF cells/cell groups and convert all FFs to them.

:cmd:ref:`deminout`
    Convert inout ports to input or output ports, if possible.

:cmd:ref:`pmuxtree`
    Transforms parallel mux cells, ``$pmux``, to trees of ``$mux`` cells.
