Synthesis starter
-----------------

.. 
   Typical phases of a synthesis flow are as follows:

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

A simple counter
~~~~~~~~~~~~~~~~

.. role:: yoscrypt(code)
   :language: yoscrypt

.. todo:: consider changing simple counter example for something with memory
   using e.g. synth_ice40 to cover more of the synth flow

This section covers an `example project`_ available in
``docs/source/code_examples/intro/``.  The project contains a simple ASIC
synthesis script (``counter.ys``), a digital design written in Verilog
(``counter.v``), and a simple CMOS cell library (``mycells.lib``).

.. _example project: https://github.com/YosysHQ/yosys/tree/krys/docs/docs/source/code_examples/intro

First, let's quickly look at the design:

.. literalinclude:: /code_examples/intro/counter.v
   :language: Verilog
   :caption: ``docs/source/code_examples/intro/counter.v``
   :linenos:
   :name: counter-v

This is a simple counter with reset and enable.  If the reset signal, ``rst``,
is high then the counter will reset to 0.  Otherwise, if the enable signal,
``en``, is high then the ``count`` register will increment by 1 each rising edge
of the clock, ``clk``.  

Loading the design
~~~~~~~~~~~~~~~~~~

Let's load the design into Yosys.  From the command line, we can call ``yosys
counter.v``.  This will open an interactive Yosys shell session and immediately
parse the code from ``counter.v`` and convert it into an Abstract Syntax Tree
(AST).  If you are interested in how this happens, there is more information in
the document, :doc:`/yosys_internals/flow/verilog_frontend`.  For now, suffice
it to say that we do this to simplify further processing of the design.  You
should see something like the following:

.. code:: console

   $ yosys counter.v

   -- Parsing `counter.v' using frontend ` -vlog2k' --

   1. Executing Verilog-2005 frontend: counter.v
   Parsing Verilog input from `counter.v' to AST representation.
   Storing AST representation for module `$abstract\counter'.
   Successfully finished Verilog frontend.

Now that we are in the interactive shell, we can call Yosys commands directly.
Let's run :yoscrypt:`hierarchy -check -top counter`.  This command declares that
the top level module is ``counter``, and that we want to expand it and any other
modules it may use.  Any other modules which were loaded are then discarded,
stopping the following commands from trying to work on them.  By passing the
``-check`` option there we are also telling the :cmd:ref:`hierarchy` command
that if the design includes any non-blackbox modules without an implementation
it should return an error.

.. todo:: more on why :cmd:ref:`hierarchy` is important

.. note::

   :cmd:ref:`hierarchy` should always be the first command after the design has
   been read.

.. use doscon for a console-like display that supports the `yosys> [command]` format.

.. code:: doscon

   yosys> hierarchy -check -top counter

   2. Executing HIERARCHY pass (managing design hierarchy).

   3. Executing AST frontend in derive mode using pre-parsed AST for module `\counter'.
   Generating RTLIL representation for module `\counter'.

   3.1. Analyzing design hierarchy..
   Top module:  \counter

   3.2. Analyzing design hierarchy..
   Top module:  \counter
   Removing unused module `$abstract\counter'.
   Removed 1 unused modules.

Our circuit now looks like this:

.. figure:: /_images/code_examples/intro/counter_00.*
   :class: width-helper
   :name: counter-hierarchy

   ``counter`` module after :cmd:ref:`hierarchy`

.. seealso:: Advanced usage docs for :doc:`/using_yosys/more_scripting/load_design`

Elaboration
~~~~~~~~~~~

Notice that block that says "PROC" in :ref:`counter-hierarchy`?  Simple
operations like ``count + 2'd1`` can be extracted from our ``always @`` block in
:ref:`counter-v`.  This gives us the ``$add`` cell we see.  But control logic,
like the ``if .. else``; and memory elements, like the ``count <='2d0``; are not
so straightforward. To handle these, let us now introduce a new command:
:doc:`/cmd/proc`.

:cmd:ref:`proc` is a macro command; running a series of other commands which
work to convert the behavioral logic of processes into multiplexers and
registers.  We go into more detail on :cmd:ref:`proc` later in
:doc:`/using_yosys/synthesis/proc`, but for now let's see what happens when we
run it.

.. figure:: /_images/code_examples/intro/counter_proc.*
   :class: width-helper

   ``counter`` module after :cmd:ref:`proc`

The ``if`` statements are now modeled with ``$mux`` cells, and the memory
consists of a ``$dff`` cell.  That's getting a bit messy now, so let's chuck in
a call to :cmd:ref:`opt`.

.. figure:: /_images/code_examples/intro/counter_01.*
   :class: width-helper

   ``counter`` module after :cmd:ref:`opt`

Much better.  We can now see that the ``$dff`` and ``$mux`` cells have been
replaced with a single ``$sdffe``, using the built-in enable and reset ports
instead.

.. todo:: a bit more on :cmd:ref:`opt` here

At this stage of a synthesis flow there are a few other commands we could run.
First off is :cmd:ref:`flatten`.  If we had any modules within our ``counter``,
this would replace them with their implementation.  Flattening the design like
this can allow for optimizations between modules which would otherwise be
missed.  Next is :doc:`/cmd/check`.

Depending on the target architecture, we might also run commands such as
:cmd:ref:`tribuf` with the ``-logic`` option and :cmd:ref:`deminout`.  These
remove tristate and inout constructs respectively, replacing them with logic
suitable for mapping to an FPGA.

.. seealso:: Advanced usage docs for :doc:`/using_yosys/synthesis/proc`

The coarse-grain representation
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

At this stage, the design is in coarse-grain representation.  It still looks
recognizable, and cells are word-level operators with parametrizable width.
There isn't much else we can do for our ``counter`` example, but this is the
stage of synthesis where we do things like const propagation, expression
rewriting, and trimming unused parts of wires.

This is also where we convert our FSMs and hard blocks like DSPs or memories.
Such elements have to be inferred from patterns in the design and there are
special passes for each.  Detection of these patterns can also be affected by
optimizations and other transformations done previously.

.. todo:: talk more about DSPs (and their associated commands)

Some of the commands we might use here are:

- :doc:`/cmd/fsm`,
- :doc:`/cmd/memory`,
- :doc:`/cmd/wreduce`,
- :doc:`/cmd/peepopt`,
- :doc:`/cmd/pmuxtree`,
- :doc:`/cmd/alumacc`, and
- :doc:`/cmd/share`.

.. seealso:: Advanced usage docs for :doc:`/using_yosys/synthesis/fsm`, and 
   :doc:`/using_yosys/synthesis/memory`

Logic gate mapping
~~~~~~~~~~~~~~~~~~

.. todo:: example_synth mapping to gates

:yoscrypt:`techmap` - Map coarse-grain RTL cells (adders, etc.) to fine-grain
logic gates (AND, OR, NOT, etc.).

When :cmd:ref:`techmap` is used without a map file, it uses a built-in map file
to map all RTL cell types to a generic library of built-in logic gates and
registers.

The built-in logic gate types are: ``$_NOT_``, ``$_AND_``, ``$_OR_``,
``$_XOR_``, and ``$_MUX_``.

See :doc:`/yosys_internals/formats/cell_library` for more about the internal
cells used.

.. figure:: /_images/code_examples/intro/counter_02.*
   :class: width-helper

   ``counter`` after :cmd:ref:`techmap`

Mapping to hardware
~~~~~~~~~~~~~~~~~~~

.. todo:: example_synth mapping to hardware

:ref:`cmos_lib`

#. :yoscrypt:`dfflibmap -liberty mycells.lib` - Map registers to available
   hardware flip-flops.
#. :yoscrypt:`abc -liberty mycells.lib` - Map logic to available hardware gates.

.. figure:: /_images/code_examples/intro/counter_03.*
   :class: width-helper

   ``counter`` after hardware cell mapping

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

:cmd:ref:`dfflegalize`
    Specify a set of supported FF cells/cell groups and convert all FFs to them.

.. seealso:: Advanced usage docs for :doc:`/yosys_internals/techmap`

.. _cmos_lib:

The CMOS cell library
^^^^^^^^^^^^^^^^^^^^^

.. literalinclude:: /code_examples/intro/mycells.lib
   :language: Liberty
   :caption: ``docs/source/code_examples/intro/mycells.lib``

The script file
~~~~~~~~~~~~~~~

#. :yoscrypt:`read_verilog -defer counter.v`
#. :yoscrypt:`clean` - Clean up the design (just the last step of
   :cmd:ref:`opt`).
#. :yoscrypt:`write_verilog synth.v` - Write final synthesis result to output
   file.

.. literalinclude:: /code_examples/intro/counter.ys
   :language: yoscrypt
   :caption: ``docs/source/code_examples/intro/counter.ys``

.. seealso:: Advanced usage docs for :doc:`/using_yosys/synthesis/synth`
