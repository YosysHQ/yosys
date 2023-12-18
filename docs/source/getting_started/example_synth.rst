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

Demo design
~~~~~~~~~~~

.. role:: yoscrypt(code)
   :language: yoscrypt

First, let's quickly look at the design we'll be synthesizing:

.. todo:: reconsider including the whole (~77 line) design like this

.. literalinclude:: /code_examples/fifo/fifo.v
   :language: Verilog
   :linenos:
   :caption: ``fifo.v``
   :name: fifo-v

.. todo:: fifo.v description

Loading the design
~~~~~~~~~~~~~~~~~~

Let's load the design into Yosys.  From the command line, we can call ``yosys
fifo.v``.  This will open an interactive Yosys shell session and immediately
parse the code from ``fifo.v`` and convert it into an Abstract Syntax Tree
(AST).  If you are interested in how this happens, there is more information in
the document, :doc:`/yosys_internals/flow/verilog_frontend`.  For now, suffice
it to say that we do this to simplify further processing of the design.  You
should see something like the following:

.. literalinclude:: /code_examples/fifo/fifo.out
   :language: console
   :start-at: $ yosys fifo.v
   :end-before: echo on

.. seealso:: Advanced usage docs for
   :doc:`/using_yosys/more_scripting/load_design`

Elaboration
~~~~~~~~~~~

Now that we are in the interactive shell, we can call Yosys commands directly.
Our overall goal is to call :yoscrypt:`synth_ice40 -top fifo`, but for now we
can run each of the commands individually for a better sense of how each part
contributes to the flow.  We will also start with just a single module;
``addr_gen``.

At the bottom of the :cmd:ref:`help` output for
:cmd:ref:`synth_ice40` is the complete list of commands called by this script.
Let's start with the section labeled ``begin``:

.. literalinclude:: /cmd/synth_ice40.rst
   :language: yoscrypt
   :start-after: begin:
   :end-before: flatten:
   :dedent:
   :caption: ``begin`` section
   :name: synth_begin

:yoscrypt:`read_verilog -D ICE40_HX -lib -specify +/ice40/cells_sim.v` loads the
iCE40 cell models which allows us to include platform specific IP blocks in our
design.  PLLs are a common example of this, where we might need to reference
``SB_PLL40_CORE`` directly rather than being able to rely on mapping passes
later.  Since our simple design doesn't use any of these IP blocks, we can safely
skip this command.

The addr_gen module
^^^^^^^^^^^^^^^^^^^

Since we're just getting started, let's instead begin with :yoscrypt:`hierarchy
-top addr_gen`.  This command declares that the top level module is ``addr_gen``,
and everything else can be discarded.

.. literalinclude:: /code_examples/fifo/fifo.v
   :language: Verilog
   :start-at: module addr_gen
   :end-at: endmodule //addr_gen
   :lineno-match:
   :caption: ``addr_gen`` module source
   :name: addr_gen-v

.. note::

   :cmd:ref:`hierarchy` should always be the first command after the design has
   been read.

.. use doscon for a console-like display that supports the `yosys> [command]` format.

.. literalinclude:: /code_examples/fifo/fifo.out
   :language: doscon
   :start-at: yosys> hierarchy -top addr_gen
   :end-before: yosys> show
   :caption: :yoscrypt:`hierarchy -top addr_gen` output

Our ``addr_gen`` circuit now looks like this:

.. figure:: /_images/code_examples/fifo/addr_gen_hier.*
   :class: width-helper
   :name: addr_gen_hier

   ``addr_gen`` module after :cmd:ref:`hierarchy`

Notice that block that says "PROC" in :ref:`addr_gen_hier`?  Simple operations
like ``addr + 1`` and ``addr == MAX_DATA-1`` can be extracted from our ``always
@`` block in :ref:`addr_gen-v`. This gives us the ``$add`` and ``$eq`` cells we
see. But control logic (like the ``if .. else``) and memory elements (like the
``addr <= 0``) are not so straightforward. To handle these, let us now introduce
the next command: :doc:`/cmd/proc`.

:cmd:ref:`proc` is a macro command like :cmd:ref:`synth_ice40`.  Rather than
modifying the design directly, it instead calls a series of other commands.  In
the case of :cmd:ref:`proc`, these sub-commands work to convert the behavioral
logic of processes into multiplexers and registers.  Let's see what happens when
we run it.

.. figure:: /_images/code_examples/fifo/addr_gen_proc.*
   :class: width-helper
   :name: addr_gen_proc

   ``addr_gen`` module after :cmd:ref:`proc`

The ``if`` statements are now modeled with ``$mux`` cells, while the register
uses an ``$adff`` cells.  If we look at the terminal output we can also see all
of the different ``proc_*`` commands being called.  We will look at each of
these in more detail in :doc:`/using_yosys/synthesis/proc`.

.. todo:: consider a brief glossary for terms like adff

The full example
^^^^^^^^^^^^^^^^

Let's now go back and check on our full design by using :yoscrypt:`hierarchy
-check -top fifo`.  By passing the ``-check`` option there we are also
telling the :cmd:ref:`hierarchy` command that if the design includes any
non-blackbox modules without an implementation it should return an error.

Note that if we tried to run this command now then we would get an error.  This
is because we already removed all of the modules other than ``addr_gen``.  We
could restart our shell session, but instead let's use two new commands:

- :doc:`/cmd/design`, and
- :doc:`/cmd/read_verilog`.

.. literalinclude:: /code_examples/fifo/fifo.out
   :language: doscon
   :start-at: design -reset
   :end-before: yosys> proc
   :caption: reloading ``fifo.v`` and running :yoscrypt:`hierarchy -check -top fifo`

Notice how this time we didn't see any of those `$abstract` modules?  That's
because when we ran ``yosys fifo.v``, the first command Yosys called was
:yoscrypt:`read_verilog -defer fifo.v`.  The ``-defer`` option there tells
:cmd:ref:`read_verilog` only read the abstract syntax tree and defer actual
compilation to a later :cmd:ref:`hierarchy` command. This is useful in cases
where the default parameters of modules yield invalid code which is not
synthesizable. This is why Yosys defers compilation automatically and is one of
the reasons why hierarchy should always be the first command after loading the
design.  If we know that our design won't run into this issue, we can skip the
``-defer``.

.. TODO:: more on why :cmd:ref:`hierarchy` is important

.. note::

   The number before a command's output increments with each command run.  Don't
   worry if your numbers don't match ours!  The output you are seeing comes from
   the same script that was used to generate the images in this document,
   included in the source as ``fifo.ys``. There are extra commands being run
   which you don't see, but feel free to try them yourself, or play around with
   different commands.  You can always start over with a clean slate by calling
   ``exit`` or hitting ``ctrl+c`` (i.e. SIGINT) and re-launching the Yosys
   interactive terminal.

We can also run :cmd:ref:`proc` now to finish off the full :ref:`synth_begin`.
Because the design schematic is quite large, we will be showing just the data
path for the ``rdata`` output.  If you would like to see the entire design for
yourself, you can do so with :doc:`/cmd/show`.  Note that the :cmd:ref:`show`
command only works with a single module, so you may need to call it with
:yoscrypt:`show fifo`.

.. figure:: /_images/code_examples/fifo/rdata_proc.*
   :class: width-helper
   :name: rdata_proc

   ``rdata`` output after :cmd:ref:`proc`

The ``fifo_reader`` block we can see there is the same as the
:ref:`addr_gen_proc` that we looked at earlier.

.. TODO:: comment on ``$memrd``

.. seealso:: Advanced usage docs for
   :doc:`/using_yosys/synthesis/proc`

Flattening
~~~~~~~~~~

At this stage of a synthesis flow there are a few other commands we could run.
In :cmd:ref:`synth_ice40` we get these:

.. literalinclude:: /cmd/synth_ice40.rst
   :language: yoscrypt
   :start-after: flatten:
   :end-before: coarse:
   :dedent:
   :name: synth_flatten
   :caption: ``flatten`` section

First off is :cmd:ref:`flatten`.  Flattening the design like this can
allow for optimizations between modules which would otherwise be missed. 

.. figure:: /_images/code_examples/fifo/rdata_flat.*
   :class: width-helper
   :name: rdata_flat

   ``rdata`` module after :cmd:ref:`flatten`

Depending on the target architecture, we might also see commands such as
:cmd:ref:`tribuf` with the ``-logic`` option and :cmd:ref:`deminout`.  These
remove tristate and inout constructs respectively, replacing them with logic
suitable for mapping to an FPGA.

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
   :linenos:
   :start-after: coarse:
   :end-before: map_ram:
   :dedent:
   :caption: ``coarse`` section
   :name: synth_coarse

.. note::

   While the iCE40 flow had a :ref:`synth_flatten` and put :cmd:ref:`proc` in
   the :ref:`synth_begin`, some synthesis scripts will instead include these in
   the :ref:`synth_coarse` section.

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
