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
   :caption: :file:`fifo.v`
   :name: fifo-v

.. todo:: fifo.v description

Loading the design
~~~~~~~~~~~~~~~~~~

Let's load the design into Yosys.  From the command line, we can call ``yosys
fifo.v``.  This will open an interactive Yosys shell session and immediately
parse the code from :ref:`fifo-v` and convert it into an Abstract Syntax Tree
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
later.  Since our simple design doesn't use any of these IP blocks, we can skip
this command for now.  Because these cell models will also be needed once we
start mapping to hardware we will still need to load them later.

.. note::

   ``+/`` is a dynamic reference to the Yosys ``share`` directory.  By default,
   this is ``/usr/local/share/yosys``.  If using a locally built version of
   Yosys from the source directory, this will be the ``share`` folder in the
   same directory.

.. _addr_gen_example:

The addr_gen module
^^^^^^^^^^^^^^^^^^^

Since we're just getting started, let's instead begin with :yoscrypt:`hierarchy
-top addr_gen`.  This command declares that the top level module is
``addr_gen``, and everything else can be discarded.

.. literalinclude:: /code_examples/fifo/fifo.v
   :language: Verilog
   :start-at: module addr_gen
   :end-at: endmodule //addr_gen
   :lineno-match:
   :caption: ``addr_gen`` module source
   :name: addr_gen-v

.. note::

   :cmd:ref:`hierarchy` should always be the first command after the design has
   been read.  By specifying the top module, :cmd:ref:`hierarchy` will also set
   the ``(* top *)`` attribute on it.  This is used by other commands that need
   to know which module is the top.

.. use doscon for a console-like display that supports the `yosys> [command]` format.

.. literalinclude:: /code_examples/fifo/fifo.out
   :language: doscon
   :start-at: yosys> hierarchy -top addr_gen
   :end-before: yosys> select
   :caption: :yoscrypt:`hierarchy -top addr_gen` output
   :name: hierarchy_output

Our ``addr_gen`` circuit now looks like this:

.. figure:: /_images/code_examples/fifo/addr_gen_hier.*
   :class: width-helper invert-helper
   :name: addr_gen_hier

   ``addr_gen`` module after :cmd:ref:`hierarchy`

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
we run it.  For now, we will call :yoscrypt:`proc -noopt` to prevent some
automatic optimizations which would normally happen.

.. figure:: /_images/code_examples/fifo/addr_gen_proc.*
   :class: width-helper invert-helper
   :name: addr_gen_proc

   ``addr_gen`` module after :yoscrypt:`proc -noopt`

There are now a few new cells from our ``always @``, which have been
highlighted.  The ``if`` statements are now modeled with ``$mux`` cells, while
the register uses an ``$adff`` cell.  If we look at the terminal output we can
also see all of the different ``proc_*`` commands being called.  We will look at
each of these in more detail in :doc:`/using_yosys/synthesis/proc`.

Notice how in the top left of :ref:`addr_gen_proc` we have a floating wire,
generated from the initial assignment of 0 to the ``addr`` wire.  However, this
initial assignment is not synthesizable, so this will need to be cleaned up
before we can generate the physical hardware.  We can do this now by calling
:cmd:ref:`clean`.  We're also going to call :cmd:ref:`opt_expr` now, which would
normally be called at the end of :cmd:ref:`proc`.  We can call both commands at
the same time by separating them with a colon and space: :yoscrypt:`opt_expr;
clean`.

.. figure:: /_images/code_examples/fifo/addr_gen_clean.*
   :class: width-helper invert-helper
   :name: addr_gen_clean

   ``addr_gen`` module after :yoscrypt:`opt_expr; clean`

You may also notice that the highlighted ``$eq`` cell input of ``255`` has
changed to ``8'11111111``.  Constant values are presented in the format
``<bit_width>'<bits>``, with 32-bit values instead using the decimal number.
This indicates that the constant input has been reduced from 32-bit wide to
8-bit wide.  This is a side-effect of running :cmd:ref:`opt_expr`, which
performs constant folding and simple expression rewriting.    For more on why
this happens, refer to :doc:`/using_yosys/synthesis/opt` and the :ref:`section
on opt_expr <adv_opt_expr>`.

.. note::

   :doc:`/cmd/clean` can also be called with two semicolons after any command,
   for example we could have called :yoscrypt:`opt_expr;;` instead of
   :yoscrypt:`opt_expr; clean`.  You may notice some scripts will end each line
   with ``;;``.  It is beneficial to run :cmd:ref:`clean` before inspecting
   intermediate products to remove disconnected parts of the circuit which have
   been left over, and in some cases can reduce the processing required in
   subsequent commands.

.. todo:: consider a brief glossary for terms like adff

.. seealso:: Advanced usage docs for
   
   - :doc:`/using_yosys/synthesis/proc`
   - :doc:`/using_yosys/synthesis/opt`

The full example
^^^^^^^^^^^^^^^^

Let's now go back and check on our full design by using :yoscrypt:`hierarchy
-check -top fifo`.  By passing the ``-check`` option there we are also telling
the :cmd:ref:`hierarchy` command that if the design includes any non-blackbox
modules without an implementation it should return an error.

Note that if we tried to run this command now then we would get an error.  This
is because we already removed all of the modules other than ``addr_gen``.  We
could restart our shell session, but instead let's use two new commands:

- :doc:`/cmd/design`, and
- :doc:`/cmd/read_verilog`.

.. literalinclude:: /code_examples/fifo/fifo.out
   :language: doscon
   :start-at: design -reset
   :end-before: yosys> proc
   :caption: reloading :file:`fifo.v` and running :yoscrypt:`hierarchy -check -top fifo`

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

.. todo:: :cmd:ref:`hierarchy` failure modes

.. note::

   The number before a command's output increments with each command run.  Don't
   worry if your numbers don't match ours!  The output you are seeing comes from
   the same script that was used to generate the images in this document,
   included in the source as :file:`fifo.ys`. There are extra commands being run
   which you don't see, but feel free to try them yourself, or play around with
   different commands.  You can always start over with a clean slate by calling
   ``exit`` or hitting :kbd:`ctrl+d` (i.e. EOF) and re-launching the Yosys
   interactive terminal.  :kbd:`ctrl+c` (i.e. SIGINT) will also end the terminal
   session but will return an error code rather than exiting gracefully.

We can also run :cmd:ref:`proc` now to finish off the full :ref:`synth_begin`.
Because the design schematic is quite large, we will be showing just the data
path for the ``rdata`` output.  If you would like to see the entire design for
yourself, you can do so with :doc:`/cmd/show`.  Note that the :cmd:ref:`show`
command only works with a single module, so you may need to call it with
:yoscrypt:`show fifo`.  :ref:`show_intro` section in
:doc:`/getting_started/scripting_intro` has more on how to use :cmd:ref:`show`.

.. figure:: /_images/code_examples/fifo/rdata_proc.*
   :class: width-helper invert-helper
   :name: rdata_proc

   ``rdata`` output after :cmd:ref:`proc`

The highlighted ``fifo_reader`` block contains an instance of the
:ref:`addr_gen_proc` that we looked at earlier.  Notice how the type is shown as
``$paramod\\addr_gen\\MAX_DATA=s32'...``.  This is a "parametric module": an
instance of the ``addr_gen`` module with the ``MAX_DATA`` parameter set to the
given value.

The other highlighted block is a ``$memrd`` cell.  At this stage of synthesis we
don't yet know what type of memory is going to be implemented, but we *do* know
that ``rdata <= data[raddr];`` could be implemented as a read from memory. Note
that the ``$memrd`` cell here is asynchronous, with both the clock and enable
signal undefined; shown with the ``1'x`` inputs.

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
   :end-before: yosys> select
   :name: flat_clean
   :caption: output of :yoscrypt:`flatten;;`

.. figure:: /_images/code_examples/fifo/rdata_flat.*
   :class: width-helper invert-helper
   :name: rdata_flat

   ``rdata`` output after :yoscrypt:`flatten;;`

.. role:: yoterm(code)
   :language: doscon

The pieces have moved around a bit, but we can see :ref:`addr_gen_proc` from
earlier has replaced the ``fifo_reader`` block in :ref:`rdata_proc`.  We can
also see that the ``addr`` output has been renamed to :file:`fifo_reader.addr`
and merged with the ``raddr`` wire feeding into the ``$memrd`` cell.  This wire
merging happened during the call to :cmd:ref:`clean` which we can see in the
:ref:`flat_clean`.

.. note:: 

   :cmd:ref:`flatten` and :cmd:ref:`clean` would normally be combined into a
   single :yoterm:`yosys> flatten;;` output, but they appear separately here as
   a side effect of using :cmd:ref:`echo` for generating the terminal style
   output.

Depending on the target architecture, this stage of synthesis might also see
commands such as :cmd:ref:`tribuf` with the ``-logic`` option and
:cmd:ref:`deminout`.  These remove tristate and inout constructs respectively,
replacing them with logic suitable for mapping to an FPGA.  Since we do not have
any such constructs in our example running these commands does not change our
design.

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

We've already come across :cmd:ref:`opt_expr`, and :cmd:ref:`opt_clean` is the
same as :cmd:ref:`clean` but with more verbose output.  The :cmd:ref:`check`
pass identifies a few obvious problems which will cause errors later.  Calling
it here lets us fail faster rather than wasting time on something we know is
impossible.

Next up is :yoscrypt:`opt -nodffe -nosdff` performing a set of simple
optimizations on the design.  This command also ensures that only a specific
subset of FF types are included, in preparation for the next command:
:doc:`/cmd/fsm`.  Both :cmd:ref:`opt` and :cmd:ref:`fsm` are macro commands
which are explored in more detail in :doc:`/using_yosys/synthesis/opt` and
:doc:`/using_yosys/synthesis/fsm` respectively.

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
   :class: width-helper invert-helper
   :name: rdata_adffe

   ``rdata`` output after :cmd:ref:`opt_dff`

.. seealso:: Advanced usage docs for
   
   - :doc:`/using_yosys/synthesis/fsm`
   - :doc:`/using_yosys/synthesis/opt`

Part 2
^^^^^^

The next group of commands performs a series of optimizations:

.. literalinclude:: /cmd/synth_ice40.rst
   :language: yoscrypt
   :start-at: wreduce
   :end-before: t:$mul
   :dedent:
   :caption: ``coarse`` section (part 2)
   :name: synth_coarse2

First up is :doc:`/cmd/wreduce`.  If we run this we get the following:

.. literalinclude:: /code_examples/fifo/fifo.out
   :language: doscon
   :start-at: yosys> wreduce
   :end-before: yosys> select
   :caption: output of :cmd:ref:`wreduce`

Looking at the data path for ``rdata``, the most relevant of these width
reductions are the ones affecting ``fifo.$flatten\fifo_reader.$add$fifo.v``.
That is the ``$add`` cell incrementing the fifo_reader address.  We can look at
the schematic and see the output of that cell has now changed.

.. todo:: pending bugfix in :cmd:ref:`wreduce` and/or :cmd:ref:`opt_clean`

.. figure:: /_images/code_examples/fifo/rdata_wreduce.*
   :class: width-helper invert-helper
   :name: rdata_wreduce

   ``rdata`` output after :cmd:ref:`wreduce`

The next two (new) commands are :doc:`/cmd/peepopt` and :doc:`/cmd/share`.
Neither of these affect our design, and they're explored in more detail in
:doc:`/using_yosys/synthesis/opt`, so let's skip over them.  :yoscrypt:`techmap
-map +/cmp2lut.v -D LUT_WIDTH=4` optimizes certain comparison operators by
converting them to LUTs instead.  The usage of :cmd:ref:`techmap` is explored
more in :doc:`/using_yosys/synthesis/techmap_synth`.

Our next command to run is
:doc:`/cmd/memory_dff`.

.. literalinclude:: /code_examples/fifo/fifo.out
   :language: doscon
   :start-at: yosys> memory_dff
   :end-before: yosys> select
   :caption: output of :cmd:ref:`memory_dff`

.. figure:: /_images/code_examples/fifo/rdata_memrdv2.*
   :class: width-helper invert-helper
   :name: rdata_memrdv2

   ``rdata`` output after :cmd:ref:`memory_dff`

As the title suggests, :cmd:ref:`memory_dff` has merged the output ``$dff`` into
the ``$memrd`` cell and converted it to a ``$memrd_v2`` (highlighted).  This has
also connected the ``CLK`` port to the ``clk`` input as it is now a synchronous
memory read with appropriate enable (``EN=1'1``) and reset (``ARST=1'0`` and
``SRST=1'0``) inputs.

.. seealso:: Advanced usage docs for
   
   - :doc:`/using_yosys/synthesis/opt`
   - :doc:`/using_yosys/synthesis/techmap_synth`
   - :doc:`/using_yosys/synthesis/memory`

Part 3
^^^^^^

The third part of the :cmd:ref:`synth_ice40` flow is a series of commands for
mapping to DSPs.  By default, the iCE40 flow will not map to the hardware DSP
blocks and will only be performed if called with the ``-dsp`` flag:
:yoscrypt:`synth_ice40 -dsp`.  While our example has nothing that could be
mapped to DSPs we can still take a quick look at the commands here and describe
what they do.

.. literalinclude:: /cmd/synth_ice40.rst
   :language: yoscrypt
   :start-at: t:$mul
   :end-before: alumacc
   :dedent:
   :caption: ``coarse`` section (part 3)
   :name: synth_coarse3

:yoscrypt:`wreduce t:$mul` performs width reduction again, this time targetting
only cells of type ``$mul``.  :yoscrypt:`techmap -map +/mul2dsp.v -map
+/ice40/dsp_map.v ... -D DSP_NAME=$__MUL16X16` uses :cmd:ref:`techmap` to map
``$mul`` cells to ``$__MUL16X16`` which are, in turn, mapped to the iCE40
``SB_MAC16``.  Any multipliers which aren't compatible with conversion to
``$__MUL16X16`` are relabelled to ``$__soft_mul`` before :cmd:ref:`chtype`
changes them back to ``$mul``.

During the mul2dsp conversion, some of the intermediate signals are marked with
the attribute ``mul2dsp``.  By calling :yoscrypt:`select a:mul2dsp` we restrict
the following commands to only operate on the cells and wires used for these
signals.  :cmd:ref:`setattr` removes the now unnecessary ``mul2dsp`` attribute.
:cmd:ref:`opt_expr` we've already come across for const folding and simple
expression rewriting, the ``-fine`` option just enables more fine-grain
optimizations.  Then we perform width reduction a final time and clear the
selection.

.. todo:: ``ice40_dsp`` is pmgen

Finally we have :cmd:ref:`ice40_dsp`: similar to the :cmd:ref:`memory_dff`
command we saw in the previous section, this merges any surrounding registers
into the ``SB_MAC16`` cell.  This includes not just the input/output registers,
but also pipeline registers and even a post-adder where applicable: turning a
multiply + add into a single multiply-accumulate.

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
we now want to extract these into ``$alu`` and ``$macc`` cells which can help
identify opportunities for reusing logic.  We do this by running
:cmd:ref:`alumacc`, which we can see produce the following changes in our
example design:

.. literalinclude:: /code_examples/fifo/fifo.out
   :language: doscon
   :start-at: yosys> alumacc
   :end-before: yosys> select
   :caption: output of :cmd:ref:`alumacc`

.. figure:: /_images/code_examples/fifo/rdata_alumacc.*
   :class: width-helper invert-helper
   :name: rdata_alumacc

   ``rdata`` output after :cmd:ref:`alumacc`

Once these cells have been inserted, the call to :cmd:ref:`opt` can combine
cells which are now identical but may have been missed due to e.g. the
difference between ``$add`` and ``$sub``.

The other new command in this part is :doc:`/cmd/memory`.  :cmd:ref:`memory` is
another macro command which we examine in more detail in
:doc:`/using_yosys/synthesis/memory`.  For this document, let us focus just on
the step most relevant to our example: :cmd:ref:`memory_collect`. Up until this
point, our memory reads and our memory writes have been totally disjoint cells;
operating on the same memory only in the abstract. :cmd:ref:`memory_collect`
combines all of the reads and writes for a memory block into a single cell.

.. figure:: /_images/code_examples/fifo/rdata_coarse.*
   :class: width-helper invert-helper
   :name: rdata_coarse

   ``rdata`` output after :cmd:ref:`memory_collect`

Looking at the schematic after running :cmd:ref:`memory_collect` we see that our
``$memrd_v2`` cell has been replaced with a ``$mem_v2`` cell named ``data``, the
same name that we used in :ref:`fifo-v`. Where before we had a single set of
signals for address and enable, we now have one set for reading (``RD_*``) and
one for writing (``WR_*``), as well as both ``WR_DATA`` input and ``RD_DATA``
output.

.. seealso:: Advanced usage docs for

   - :doc:`/using_yosys/synthesis/opt`
   - :doc:`/using_yosys/synthesis/memory`

Final note
^^^^^^^^^^

Having now reached the end of the the coarse-grain representation, we could also
have gotten here by running :yoscrypt:`synth_ice40 -top fifo -run :map_ram`
after loading the design.  The :yoscrypt:`-run <from_label>:<to_label>` option
with an empty ``<from_label>`` starts from the :ref:`synth_begin`, while the
``<to_label>`` runs up to but including the :ref:`map_ram`.

Hardware mapping
~~~~~~~~~~~~~~~~

The remaining sections each map a different type of hardware and are much more
architecture dependent than the previous sections.  As such we will only be
looking at each section very briefly.

If you skipped calling :yoscrypt:`read_verilog -D ICE40_HX -lib -specify
+/ice40/cells_sim.v` earlier, do it now.

Memory blocks
^^^^^^^^^^^^^

Mapping to hard memory blocks uses a combination of :cmd:ref:`memory_libmap` and
:cmd:ref:`techmap`.

.. literalinclude:: /cmd/synth_ice40.rst
   :language: yoscrypt
   :start-after: map_ram:
   :end-before: map_ffram:
   :dedent:
   :name: map_ram
   :caption: ``map_ram`` section

.. figure:: /_images/code_examples/fifo/rdata_map_ram.*
   :class: width-helper invert-helper
   :name: rdata_map_ram

   ``rdata`` output after :ref:`map_ram`

The :ref:`map_ram` converts the generic ``$mem_v2`` into the iCE40
``SB_RAM40_4K`` (highlighted). We can also see the memory address has been
remapped, and the data bits have been reordered (or swizzled).  There is also
now a ``$mux`` cell controlling the value of ``rdata``.  In :ref:`fifo-v` we
wrote our memory as read-before-write, however the ``SB_RAM40_4K`` has undefined
behaviour when reading from and writing to the same address in the same cycle.
As a result, extra logic is added so that the generated circuit matches the
behaviour of the verilog.  :ref:`no_rw_check` describes how we could change our
verilog to match our hardware instead.

If we run :cmd:ref:`memory_libmap` under the :cmd:ref:`debug` command we can see
candidates which were identified for mapping, along with the costs of each and
what logic requires emulation.

.. literalinclude:: /code_examples/fifo/fifo.libmap
   :language: doscon
   :lines: 2, 6-

The ``$__ICE40_RAM4K_`` cell is defined in the file |techlibs/ice40/brams.txt|_,
with the mapping to ``SB_RAM40_4K`` done by :cmd:ref:`techmap` using
|techlibs/ice40/brams_map.v|_.  Any leftover memory cells are then converted
into flip flops (the ``logic fallback``) with :cmd:ref:`memory_map`.

.. |techlibs/ice40/brams.txt| replace:: :file:`techlibs/ice40/brams.txt`
.. _techlibs/ice40/brams.txt: https://github.com/YosysHQ/yosys/tree/main/techlibs/ice40/brams.txt
.. |techlibs/ice40/brams_map.v| replace:: :file:`techlibs/ice40/brams_map.v`
.. _techlibs/ice40/brams_map.v: https://github.com/YosysHQ/yosys/tree/main/techlibs/ice40/brams_map.v

.. literalinclude:: /cmd/synth_ice40.rst
   :language: yoscrypt
   :start-after: map_ffram:
   :end-before: map_gates:
   :dedent:
   :name: map_ffram
   :caption: ``map_ffram`` section

.. figure:: /_images/code_examples/fifo/rdata_map_ffram.*
   :class: width-helper invert-helper
   :name: rdata_map_ffram

   ``rdata`` output after :ref:`map_ffram`

.. note::

   The visual clutter on the ``RDATA`` output port (highlighted) is an
   unfortunate side effect of :cmd:ref:`opt_clean` on the swizzled data bits. In
   connecting the ``$mux`` input port directly to ``RDATA`` to reduce the number
   of wires, the ``$techmap579\data.0.0.RDATA`` wire becomes more visually
   complex.

.. seealso:: Advanced usage docs for
   
   - :doc:`/using_yosys/synthesis/techmap_synth`
   - :doc:`/using_yosys/synthesis/memory`

Arithmetic
^^^^^^^^^^

Uses :cmd:ref:`techmap` to map basic arithmetic logic to hardware.  This sees
somewhat of an explosion in cells as multi-bit ``$mux`` and ``$adffe`` are
replaced with single-bit ``$_MUX_`` and ``$_DFFE_PP0P_`` cells, while the
``$alu`` is replaced with primitive ``$_OR_`` and ``$_NOT_`` gates and a
``$lut`` cell.

.. literalinclude:: /cmd/synth_ice40.rst
   :language: yoscrypt
   :start-after: map_gates:
   :end-before: map_ffs:
   :dedent:
   :name: map_gates
   :caption: ``map_gates`` section

.. figure:: /_images/code_examples/fifo/rdata_map_gates.*
   :class: width-helper invert-helper
   :name: rdata_map_gates

   ``rdata`` output after :ref:`map_gates`

.. seealso:: Advanced usage docs for
   :doc:`/using_yosys/synthesis/techmap_synth`

Flip-flops
^^^^^^^^^^

Convert FFs to the types supported in hardware with :cmd:ref:`dfflegalize`, and
then use :cmd:ref:`techmap` to map them.  In our example, this converts the
``$_DFFE_PP0P_`` cells to ``SB_DFFER``.

We also run :cmd:ref:`simplemap` here to convert any remaining cells which could
not be mapped to hardware into gate-level primitives.  This includes optimizing
``$_MUX_`` cells where one of the inputs is a constant ``1'0``, replacing it
instead with an ``$_AND_`` cell.

.. literalinclude:: /cmd/synth_ice40.rst
   :language: yoscrypt
   :start-after: map_ffs:
   :end-before: map_luts:
   :dedent:
   :name: map_ffs
   :caption: ``map_ffs`` section

.. figure:: /_images/code_examples/fifo/rdata_map_ffs.*
   :class: width-helper invert-helper
   :name: rdata_map_ffs

   ``rdata`` output after :ref:`map_ffs`

.. seealso:: Advanced usage docs for
   :doc:`/using_yosys/synthesis/techmap_synth`

LUTs
^^^^

:cmd:ref:`abc` and :cmd:ref:`techmap` are used to map LUTs; converting primitive
cell types to use ``$lut`` and ``SB_CARRY`` cells.  Note that the iCE40 flow
uses :cmd:ref:`abc9` rather than :cmd:ref:`abc`. For more on what these do, and
what the difference between these two commands are, refer to
:doc:`/using_yosys/synthesis/abc`.

.. literalinclude:: /cmd/synth_ice40.rst
   :language: yoscrypt
   :start-after: map_luts:
   :end-before: map_cells:
   :dedent:
   :name: map_luts
   :caption: ``map_luts`` section

.. figure:: /_images/code_examples/fifo/rdata_map_luts.*
   :class: width-helper invert-helper
   :name: rdata_map_luts

   ``rdata`` output after :ref:`map_luts`

Finally we use :cmd:ref:`techmap` to map the generic ``$lut`` cells to iCE40
``SB_LUT4`` cells.

.. literalinclude:: /cmd/synth_ice40.rst
   :language: yoscrypt
   :start-after: map_cells:
   :end-before: check:
   :dedent:
   :name: map_cells
   :caption: ``map_cells`` section

.. figure:: /_images/code_examples/fifo/rdata_map_cells.*
   :class: width-helper invert-helper
   :name: rdata_map_cells

   ``rdata`` output after :ref:`map_cells`

.. seealso:: Advanced usage docs for
   
   - :doc:`/using_yosys/synthesis/techmap_synth`
   - :doc:`/using_yosys/synthesis/abc`

Other cells
^^^^^^^^^^^

The following commands may also be used for mapping other cells:

:cmd:ref:`hilomap`
    Some architectures require special driver cells for driving a constant hi or
    lo value. This command replaces simple constants with instances of such
    driver cells.

:cmd:ref:`iopadmap`
    Top-level input/outputs must usually be implemented using special I/O-pad
    cells. This command inserts such cells to the design.

These commands tend to either be in the :ref:`map_cells` or after the
:ref:`check` depending on the flow.

Final steps
~~~~~~~~~~~~

The next section of the iCE40 synth flow performs some sanity checking and final
tidy up:

.. literalinclude:: /cmd/synth_ice40.rst
   :language: yoscrypt
   :start-after: check:
   :end-before: blif:
   :dedent:
   :name: check
   :caption: ``check`` section

The new commands here are:

- :doc:`/cmd/autoname`,
- :doc:`/cmd/stat`, and
- :doc:`/cmd/blackbox`.

The output from :cmd:ref:`stat` is useful for checking resource utilization;
providing a list of cells used in the design and the number of each, as well as
the number of other resources used such as wires and processes.  For this
design, the final call to :cmd:ref:`stat` should look something like the
following:

.. literalinclude:: /code_examples/fifo/fifo.stat
   :language: doscon
   :start-at: yosys> stat -top fifo

Note that the :yoscrypt:`-top fifo` here is optional.  :cmd:ref:`stat` will
automatically use the module with the ``top`` attribute set, which ``fifo`` was
when we called :cmd:ref:`hierarchy`.  If no module is marked ``top``, then stats
will be shown for each module selected.

The :cmd:ref:`stat` output is also useful as a kind of sanity-check: Since we
have already run :cmd:ref:`proc`, we wouldn't expect there to be any processes.
We also expect ``data`` to use hard memory; if instead of an ``SB_RAM40_4K`` saw
a high number of flip-flops being used we might suspect something was wrong.

If we instead called :cmd:ref:`stat` immediately after :yoscrypt:`read_verilog
fifo.v` we would see something very different:

.. literalinclude:: /code_examples/fifo/fifo.stat
   :language: doscon
   :start-at: yosys> stat
   :end-before: yosys> stat -top fifo

Notice how ``fifo`` and ``addr_gen`` are listed separately, and the statistics
for ``fifo`` show 2 ``addr_gen`` modules.  Because this is before the memory has
been mapped, we also see that there is 1 memory with 2048 memory bits; matching
our 8-bit wide ``data`` memory with 256 values (:math:`8*256=2048`).

Synthesis output
^^^^^^^^^^^^^^^^

The iCE40 synthesis flow has the following output modes available:

- :doc:`/cmd/write_blif`,
- :doc:`/cmd/write_edif`, and
- :doc:`/cmd/write_json`.

As an example, if we called :yoscrypt:`synth_ice40 -top fifo -json fifo.json`,
our synthesized ``fifo`` design will be output as :file:`fifo.json`.  We can
then read the design back into Yosys with :cmd:ref:`read_json`, but make sure
you use :yoscrypt:`design -reset` or open a new interactive terminal first.  The
JSON output we get can also be loaded into `nextpnr`_ to do place and route; but
that is beyond the scope of this documentation.

.. _nextpnr: https://github.com/YosysHQ/nextpnr

.. seealso:: :doc:`/cmd/synth_ice40`
