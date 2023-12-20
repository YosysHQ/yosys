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
   :end-before: yosys> select
   :caption: :yoscrypt:`hierarchy -top addr_gen` output

Our ``addr_gen`` circuit now looks like this:

.. figure:: /_images/code_examples/fifo/addr_gen_hier.*
   :class: width-helper
   :name: addr_gen_hier

   ``addr_gen`` module after :cmd:ref:`hierarchy`

.. todo:: how to highlight PROC blocks? 
   They seem to be replaced in ``show``, so the selection never matches

Simple operations like ``addr + 1`` and ``addr == MAX_DATA-1`` can be extracted
from our ``always @`` block in :ref:`addr_gen-v`. This gives us the highlighted
``$add`` and ``$eq`` cells we see. But control logic (like the ``if .. else``)
and memory elements (like the ``addr <= 0``) are not so straightforward.  These
get put into "processes", shown in the schematic as ``PROC``.  Note how the
second line refers to the line numbers of the start/end of the corresponding
``always @`` block.  In the case of an ``initial`` block, we instead see the
``PROC`` referring to line 0.

To handle these, let us now introduce the next command: :doc:`/cmd/proc`.
:cmd:ref:`proc` is a macro command like :cmd:ref:`synth_ice40`.  Rather than
modifying the design directly, it instead calls a series of other commands.  In
the case of :cmd:ref:`proc`, these sub-commands work to convert the behavioral
logic of processes into multiplexers and registers.  Let's see what happens when
we run it.

.. figure:: /_images/code_examples/fifo/addr_gen_proc.*
   :class: width-helper
   :name: addr_gen_proc

   ``addr_gen`` module after :cmd:ref:`proc`

There are now a few new cells from our ``always @``, which have been
highlighted.  The ``if`` statements are now modeled with ``$mux`` cells, while
the register uses an ``$adff`` cell.  If we look at the terminal output we can
also see all of the different ``proc_*`` commands being called.  We will look at
each of these in more detail in :doc:`/using_yosys/synthesis/proc`.

.. TODO:: intro ``opt_expr``
   :doc:`/cmd/opt_expr`

   - by default called at the end of :cmd:ref:`proc`

Notice how in the top left of :ref:`addr_gen_proc` we have a floating wire,
generated from the initial assignment of 0 to the ``addr`` wire.  However, this
initial assignment is not synthesizable, so this will need to be cleaned up
before we can generate the physical hardware.  We can do this now by calling
:cmd:ref:`opt_clean`:

.. figure:: /_images/code_examples/fifo/addr_gen_clean.*
   :class: width-helper
   :name: addr_gen_clean

   ``addr_gen`` module after :cmd:ref:`opt_clean`

.. TODO:: more on opt_clean
   :doc:`/cmd/opt_clean`

   - :cmd:ref:`clean` for short, ``;;`` for even shorter
   - final command of :cmd:ref:`opt`
   - can run at any time

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

The highlighted ``fifo_reader`` block contains an instance of the
:ref:`addr_gen_proc` that we looked at earlier.  Notice how the type is shown as
``$paramod\\addr_gen\\MAX_DATA=s32'...``.  This is a "parametric module"; an
instance of the ``addr_gen`` module with the ``MAX_DATA`` set to the given
value.

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

First off is :cmd:ref:`flatten`.  Flattening the design like this can allow for
optimizations between modules which would otherwise be missed.  Let's run
:yoscrypt:`flatten;;` on our design.

.. literalinclude:: /code_examples/fifo/fifo.out
   :language: doscon
   :start-at: yosys> flatten
   :end-before: yosys> show
   :name: flat_clean
   :caption: output of :yoscrypt:`flatten;;`

.. figure:: /_images/code_examples/fifo/rdata_flat.*
   :class: width-helper
   :name: rdata_flat

   ``rdata`` output after :yoscrypt:`flatten;;`

We can now see both :ref:`rdata_proc` and :ref:`addr_gen_proc` together.  Note
that in the :ref:`flat_clean` we see above has two separate calls: one to
:cmd:ref:`flatten` and one to :cmd:ref:`clean`.  In an interactive terminal the
output of both commands will be combined into the single `yosys> flatten;;`
output.

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

.. note::

   While the iCE40 flow had a :ref:`synth_flatten` and put :cmd:ref:`proc` in
   the :ref:`synth_begin`, some synthesis scripts will instead include these in
   this section.

Part 1
^^^^^^

In the iCE40 flow, we start with the following commands:

.. literalinclude:: /cmd/synth_ice40.rst
   :language: yoscrypt
   :start-after: coarse:
   :end-before: wreduce
   :dedent:
   :caption: ``coarse`` section (part 1)
   :name: synth_coarse1

The first few commands are relatively straightforward, and we've already come
across :cmd:ref:`opt_clean` and :cmd:ref:`opt_expr`.  The :cmd:ref:`check` pass
identifies a few obvious problems which will cause errors later.  Calling it
here lets us fail faster rather than wasting time on something we know is
impossible.

Next up is :yoscrypt:`opt -nodffe -nosdff` performing a set of simple
optimizations on the design.  This command also ensures that only a specific
subset of FF types are included, in preparation for the next command:
:doc:`/cmd/fsm`.  Both :cmd:ref:`opt` and :cmd:ref:`fsm` are macro commands
which are explored in more detail in :doc:`/using_yosys/synthesis/fsm` and
:doc:`/using_yosys/synthesis/opt` respectively.

Up until now, the data path for ``rdata`` has remained the same since
:ref:`rdata_flat`.  However the next call to :cmd:ref:`opt` does cause a change.
Specifically, the call to :cmd:ref:`opt_dff` without the ``-nodffe -nosdff``
options is able to fold one of the ``$mux`` cells into the ``$adff`` to form an
``$adffe`` cell; highlighted below:

.. literalinclude:: /code_examples/fifo/fifo.out
   :language: doscon
   :start-at: yosys> opt_dff
   :end-before: yosys> select
   :caption: output of :cmd:ref:`opt_dff`

.. figure:: /_images/code_examples/fifo/rdata_adffe.*
   :class: width-helper
   :name: rdata_adffe

   ``rdata`` output after :cmd:ref:`opt_dff`

.. seealso:: Advanced usage docs for
   
   - :doc:`/using_yosys/synthesis/fsm`
   - :doc:`/using_yosys/synthesis/opt`

Part 2
^^^^^^

.. literalinclude:: /cmd/synth_ice40.rst
   :language: yoscrypt
   :start-at: wreduce
   :end-before: t:$mul
   :dedent:
   :caption: ``coarse`` section (part 2)
   :name: synth_coarse2

The next three (new) commands are :doc:`/cmd/wreduce`, :doc:`/cmd/peepopt`, and
:doc:`/cmd/share`.  None of these affect our design either, so let's skip over
them.  :yoscrypt:`techmap -map +/cmp2lut.v -D LUT_WIDTH=4` optimizes certain
comparison operators by converting them to LUTs instead.  The usage of
:cmd:ref:`techmap` is explored more in
:doc:`/using_yosys/synthesis/techmap_synth`.

Our next command to run is
:doc:`/cmd/memory_dff`.

.. literalinclude:: /code_examples/fifo/fifo.out
   :language: doscon
   :start-at: yosys> memory_dff
   :end-before: yosys> select
   :caption: output of :cmd:ref:`memory_dff`

.. figure:: /_images/code_examples/fifo/rdata_memrdv2.*
   :class: width-helper
   :name: rdata_memrdv2

   ``rdata`` output after :cmd:ref:`memory_dff`

As the title suggests, :cmd:ref:`memory_dff` has merged the output ``$dff`` into
the ``$memrd`` cell and converted it to a ``$memrd_v2`` (highlighted).

.. seealso:: Advanced usage docs for
   
   - :doc:`/using_yosys/synthesis/opt`
   - :doc:`/using_yosys/synthesis/techmap_synth`
   - :doc:`/using_yosys/synthesis/memory`

Part 3
^^^^^^

The third part of the :cmd:ref:`synth_ice40` flow is a series of commands for
mapping to DSPs.

.. literalinclude:: /cmd/synth_ice40.rst
   :language: yoscrypt
   :start-at: t:$mul
   :end-before: alumacc
   :dedent:
   :caption: ``coarse`` section (part 3)
   :name: synth_coarse3

.. TODO:: more on DSP mapping

.. seealso:: Advanced usage docs for
   :doc:`/using_yosys/synthesis/techmap_synth`

Part 4
^^^^^^

That brings us to the fourth and final part for the iCE40 synthesis flow:

.. literalinclude:: /cmd/synth_ice40.rst
   :language: yoscrypt
   :start-at: alumacc
   :end-before: map_ram:
   :dedent:
   :caption: ``coarse`` section (part 4)
   :name: synth_coarse4

Where before each type of arithmetic operation had its own cell, e.g. ``$add``,
we now want to extract these into ``$alu`` and ``$macc`` cells which can be
mapped to hard blocks.  We do this by running :cmd:ref:`alumacc`, which we can
see produce the following changes in our example design:

.. literalinclude:: /code_examples/fifo/fifo.out
   :language: doscon
   :start-at: yosys> alumacc
   :end-before: yosys> select
   :caption: output of :cmd:ref:`alumacc`

.. figure:: /_images/code_examples/fifo/rdata_alumacc.*
   :class: width-helper
   :name: rdata_alumacc

   ``rdata`` output after :cmd:ref:`alumacc`

.. TODO:: discuss :cmd:ref:`memory_collect` and ``$mem_v2``

.. figure:: /_images/code_examples/fifo/rdata_coarse.*
   :class: width-helper
   :name: rdata_coarse

   ``rdata`` output after :yoscrypt:`memory -nomap`

We could also have gotten here by running :yoscrypt:`synth_ice40 -top fifo -run
begin:map_ram` after loading the design.

.. seealso:: Advanced usage docs for
   :doc:`/using_yosys/synthesis/memory`

Hardware mapping
~~~~~~~~~~~~~~~~

The remaining sections each map a different type of hardware and are much more
architecture dependent than the previous sections.  As such we will only be
looking at each section very briefly.

Memory blocks
^^^^^^^^^^^^^

Mapping to hard memory blocks uses a combination of :cmd:ref:`memory_libmap`,
:cmd:ref:`memory_map`, and :cmd:ref:`techmap`.

.. TODO:: ``$mem_v2`` -> ``SB_RAM40_4K``

.. literalinclude:: /cmd/synth_ice40.rst
   :language: yoscrypt
   :start-after: map_ram:
   :end-before: map_ffram:
   :dedent:
   :name: map_ram
   :caption: ``map_ram`` section

.. figure:: /_images/code_examples/fifo/rdata_map_ram.*
   :class: width-helper
   :name: rdata_map_ram

   ``rdata`` output after :ref:`map_ram`

.. literalinclude:: /cmd/synth_ice40.rst
   :language: yoscrypt
   :start-after: map_ffram:
   :end-before: map_gates:
   :dedent:
   :name: map_ffram
   :caption: ``map_ffram`` section

.. figure:: /_images/code_examples/fifo/rdata_map_ffram.*
   :class: width-helper
   :name: rdata_map_ffram

   ``rdata`` output after :ref:`map_ffram`

.. seealso:: Advanced usage docs for
   
   - :doc:`/using_yosys/synthesis/techmap_synth`
   - :doc:`/using_yosys/synthesis/memory`

Arithmetic
^^^^^^^^^^

Uses :cmd:ref:`techmap`.

.. TODO:: example_synth/Arithmetic

.. literalinclude:: /cmd/synth_ice40.rst
   :language: yoscrypt
   :start-after: map_gates:
   :end-before: map_ffs:
   :dedent:
   :name: map_gates
   :caption: ``map_gates`` section

.. figure:: /_images/code_examples/fifo/rdata_map_gates.*
   :class: width-helper
   :name: rdata_map_gates

   ``rdata`` output after :ref:`map_gates`

.. seealso:: Advanced usage docs for
   :doc:`/using_yosys/synthesis/techmap_synth`

Flip-flops
^^^^^^^^^^

Convert FFs to the types supported in hardware with :cmd:ref:`dfflegalize`, and
then use :cmd:ref:`techmap` to map them.  We also run :cmd:ref:`simplemap` here
to convert any remaining cells which could not be mapped to hardware into
gate-level primitives.

.. literalinclude:: /cmd/synth_ice40.rst
   :language: yoscrypt
   :start-after: map_ffs:
   :end-before: map_luts:
   :dedent:
   :name: map_ffs
   :caption: ``map_ffs`` section

.. figure:: /_images/code_examples/fifo/rdata_map_ffs.*
   :class: width-helper
   :name: rdata_map_ffs

   ``rdata`` output after :ref:`map_ffs`

.. seealso:: Advanced usage docs for
   :doc:`/using_yosys/synthesis/techmap_synth`

LUTs
^^^^

:cmd:ref:`abc` and :cmd:ref:`techmap` are used to map LUTs.  Note that the iCE40
flow uses :cmd:ref:`abc` rather than :cmd:ref:`abc9`.  For more on what these
do, and what the difference between these two commands are, refer to
:doc:`/using_yosys/synthesis/abc`.

.. literalinclude:: /cmd/synth_ice40.rst
   :language: yoscrypt
   :start-after: map_luts:
   :end-before: map_cells:
   :dedent:
   :name: map_luts
   :caption: ``map_luts`` section

.. figure:: /_images/code_examples/fifo/rdata_map_luts.*
   :class: width-helper
   :name: rdata_map_luts

   ``rdata`` output after :ref:`map_luts`

.. seealso:: Advanced usage docs for
   
   - :doc:`/using_yosys/synthesis/techmap_synth`
   - :doc:`/using_yosys/synthesis/abc`

Other cells
^^^^^^^^^^^

Seems to be wide LUTs into individual LUTs using :cmd:ref:`techmap`.

.. literalinclude:: /cmd/synth_ice40.rst
   :language: yoscrypt
   :start-after: map_cells:
   :end-before: check:
   :dedent:
   :name: map_cells
   :caption: ``map_cells`` section

.. figure:: /_images/code_examples/fifo/rdata_map_cells.*
   :class: width-helper
   :name: rdata_map_cells

   ``rdata`` output after :ref:`map_cells`

.. TODO:: example_synth other cells

:cmd:ref:`hilomap`
    Some architectures require special driver cells for driving a constant hi or
    lo value. This command replaces simple constants with instances of such
    driver cells.

:cmd:ref:`iopadmap`
    Top-level input/outputs must usually be implemented using special I/O-pad
    cells. This command inserts such cells to the design.

.. seealso:: Advanced usage docs for
   :doc:`/yosys_internals/techmap`

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
