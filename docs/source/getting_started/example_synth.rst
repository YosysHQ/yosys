Synthesis starter
-----------------

This page will be a guided walkthrough of the prepackaged iCE40 FPGA synthesis
script - :cmd:ref:`synth_ice40`.  We will take a simple design through each
step, looking at the commands being called and what they do to the design. While
:cmd:ref:`synth_ice40` is specific to the iCE40 platform, most of the operations
we will be discussing are common across the majority of FPGA synthesis scripts.
Thus, this document will provide a good foundational understanding of how
synthesis in Yosys is performed, regardless of the actual architecture being
used.

.. seealso:: Advanced usage docs for
   :doc:`/using_yosys/synthesis/synth`

A simple counter
~~~~~~~~~~~~~~~~

.. role:: yoscrypt(code)
   :language: yoscrypt

.. TODO:: replace counter.v with a (slightly) more complex design 
   which includes hard blocks and maybe an FSM

First, let's quickly look at the design we'll be synthesizing:

.. literalinclude:: /code_examples/intro/counter.v
   :language: Verilog
   :caption: ``docs/source/code_examples/intro/counter.v``
   :linenos:

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

.. seealso:: Advanced usage docs for
   :doc:`/using_yosys/more_scripting/load_design`

Elaboration
~~~~~~~~~~~

Now that we are in the interactive shell, we can call Yosys commands directly.
Our overall goal is to call :yoscrypt:`synth_ice40 -top counter`, but for now we
can run each of the commands individually for a better sense of how each part
contributes to the flow.  At the bottom of the :cmd:ref:`help` output for
:cmd:ref:`synth_ice40` is the complete list of commands called by this script.
Let's start with the section labeled ``begin``:

.. literalinclude:: /cmd/synth_ice40.rst
   :language: yoscrypt
   :start-after: begin:
   :end-before: flatten:
   :dedent:
   :caption: ``begin`` section

:yoscrypt:`read_verilog -D ICE40_HX -lib -specify +/ice40/cells_sim.v` loads the
iCE40 cell models which allows us to include platform specific IP blocks in our
design.  PLLs are a common example of this, where we might need to reference
``SB_PLL40_CORE`` directly rather than being able to rely on mapping passes
later.  Since our simple design doesn't use any of these IP blocks, we can safely
skip this command.

Let's instead start with run :yoscrypt:`hierarchy -check -top counter`.  This
command declares that the top level module is ``counter``, and that we want to
expand it and any other modules it may use.  Any other modules which were loaded
are then discarded, preventing the subsequent commands from trying to work on
them. By passing the ``-check`` option there we are also telling the
:cmd:ref:`hierarchy` command that if the design includes any non-blackbox
modules without an implementation it should return an error.

.. TODO:: more on why :cmd:ref:`hierarchy` is important

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

   ``counter`` module after :cmd:ref:`hierarchy`

Notice that block that says "PROC" in :ref:`counter-hierarchy`?  Simple
operations like ``count + 2'd1`` can be extracted from our ``always @`` block in
:ref:`counter-v`.  This gives us the ``$add`` cell we see.  But control logic
(like the ``if .. else``) and memory elements (like the ``count <='2d0``) are
not so straightforward. To handle these, let us now introduce the next command:
:doc:`/cmd/proc`.

:cmd:ref:`proc` is a macro command like :cmd:ref:`synth_ice40`.  Rather than
processing our design itself, it instead calls a series of other commands.  In
the case of :cmd:ref:`proc`, these sub-commands work to convert the behavioral
logic of processes into multiplexers and registers.  We go into more detail on
:cmd:ref:`proc` later in :doc:`/using_yosys/synthesis/proc`, but for now let's
see what happens when we run it.

.. figure:: /_images/code_examples/intro/counter_proc.*
   :class: width-helper

   ``counter`` module after :cmd:ref:`proc`

The ``if`` statements are now modeled with ``$mux`` cells, and the memory
consists of a ``$dff`` cell.

.. seealso:: Advanced usage docs for
   :doc:`/using_yosys/synthesis/proc`

Flattening
~~~~~~~~~~

At this stage of a synthesis flow there are a few other commands we could run.
First off is :cmd:ref:`flatten`.  If we had any modules within our ``counter``,
this would replace them with their implementation.  Flattening the design like
this can allow for optimizations between modules which would otherwise be
missed.

Depending on the target architecture, we might also run commands such as
:cmd:ref:`tribuf` with the ``-logic`` option and :cmd:ref:`deminout`.  These
remove tristate and inout constructs respectively, replacing them with logic
suitable for mapping to an FPGA.

.. literalinclude:: /cmd/synth_ice40.rst
   :language: yoscrypt
   :start-after: flatten:
   :end-before: coarse:
   :dedent:
   :name: flatten
   :caption: ``flatten`` section

The iCE40 flow puts these commands into thier own :ref:`flatten`,
while some synthesis scripts will instead include them in the next section.

The coarse-grain representation
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

At this stage, the design is in coarse-grain representation.  It still looks
recognizable, and cells are word-level operators with parametrizable width. This
is the stage of synthesis where we do things like const propagation, expression
rewriting, and trimming unused parts of wires.

This is also where we convert our FSMs and hard blocks like DSPs or memories.
Such elements have to be inferred from patterns in the design and there are
special passes for each.  Detection of these patterns can also be affected by
optimizations and other transformations done previously.

In the iCE40 flow we get all the following commands:

.. literalinclude:: /cmd/synth_ice40.rst
   :language: yoscrypt
   :start-after: coarse:
   :end-before: map_ram:
   :dedent:
   :caption: ``coarse`` section

.. TODO:: talk more about DSPs (and their associated commands)

.. TODO:: example_syth ``coarse`` section

Some of the commands we might use here are:

- :doc:`/cmd/opt_expr`,
- :doc:`/cmd/opt_clean`,
- :doc:`/cmd/check`,
- :doc:`/cmd/opt`,
- :doc:`/cmd/fsm`,
- :doc:`/cmd/wreduce`,
- :doc:`/cmd/peepopt`,
- :doc:`/cmd/memory`,
- :doc:`/cmd/pmuxtree`,
- :doc:`/cmd/alumacc`, and
- :doc:`/cmd/share`.

.. seealso:: Advanced usage docs for
   :doc:`/using_yosys/synthesis/fsm`,
   :doc:`/using_yosys/synthesis/memory`, and
   :doc:`/using_yosys/synthesis/opt`

Hardware mapping
~~~~~~~~~~~~~~~~

.. TODO:: example_synth hardware mapping sections

.. literalinclude:: /cmd/synth_ice40.rst
   :language: yoscrypt
   :start-after: map_ram:
   :end-before: map_ffram:
   :dedent:
   :name: map_ram
   :caption: ``map_ram`` section

.. literalinclude:: /cmd/synth_ice40.rst
   :language: yoscrypt
   :start-after: map_ffram:
   :end-before: map_gates:
   :dedent:
   :name: map_ffram
   :caption: ``map_ffram`` section

.. literalinclude:: /cmd/synth_ice40.rst
   :language: yoscrypt
   :start-after: map_gates:
   :end-before: map_ffs:
   :dedent:
   :name: map_gates
   :caption: ``map_gates`` section

.. literalinclude:: /cmd/synth_ice40.rst
   :language: yoscrypt
   :start-after: map_ffs:
   :end-before: map_luts:
   :dedent:
   :name: map_ffs
   :caption: ``map_ffs`` section

.. literalinclude:: /cmd/synth_ice40.rst
   :language: yoscrypt
   :start-after: map_luts:
   :end-before: map_cells:
   :dedent:
   :name: map_luts
   :caption: ``map_luts`` section

.. literalinclude:: /cmd/synth_ice40.rst
   :language: yoscrypt
   :start-after: map_cells:
   :end-before: check:
   :dedent:
   :name: map_cells
   :caption: ``map_cells`` section

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

.. seealso:: Advanced usage docs for
   :doc:`/yosys_internals/techmap`, and
   :doc:`/using_yosys/synthesis/memory`.

Final steps
~~~~~~~~~~~~

.. TODO:: example_synth final steps (check section and outputting)

.. literalinclude:: /cmd/synth_ice40.rst
   :language: yoscrypt
   :start-after: check:
   :end-before: blif:
   :dedent:
   :name: check
   :caption: ``check`` section

- :doc:`/cmd/check`
- :doc:`/cmd/autoname`
- :doc:`/cmd/stat`
