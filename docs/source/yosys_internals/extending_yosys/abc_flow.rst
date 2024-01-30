Setting up a flow for ABC9
--------------------------

Much of the configuration comes from attributes and ``specify`` blocks in
Verilog simulation models.

``specify`` syntax
~~~~~~~~~~~~~~~~~~

Since ``specify`` is a relatively obscure part of the Verilog standard, a quick
guide to the syntax:

.. code-block:: verilog

   specify                           // begins a specify block
     (A => B) = 123;                 // simple combinational path from A to B with a delay of 123.
     (A *> B) = 123;                 // simple combinational path from A to all bits of B with a delay of 123 for all.
     if (FOO) (A => B) = 123;        // paths may apply under specific conditions.
     (posedge CLK => (Q : D)) = 123; // combinational path triggered on the positive edge of CLK; used for clock-to-Q arrival paths.
     $setup(A, posedge CLK, 123);    // setup constraint for an input relative to a clock.
   endspecify                        // ends a specify block

By convention, all delays in ``specify`` blocks are in integer picoseconds.
Files containing ``specify`` blocks should be read with the ``-specify`` option
to :cmd:ref:`read_verilog` so that they aren't skipped.

LUTs
^^^^

LUTs need to be annotated with an ``(* abc9_lut=N *)`` attribute, where ``N`` is
the relative area of that LUT model. For example, if an architecture can combine
LUTs to produce larger LUTs, then the combined LUTs would have increasingly
larger ``N``. Conversely, if an architecture can split larger LUTs into smaller
LUTs, then the smaller LUTs would have smaller ``N``.

LUTs are generally specified with simple combinational paths from the LUT inputs
to the LUT output.

DFFs
^^^^

DFFs should be annotated with an ``(* abc9_flop *)`` attribute, however ABC9 has
some specific requirements for this to be valid: - the DFF must initialise to
zero (consider using :cmd:ref:`dfflegalize` to ensure this). - the DFF cannot
have any asynchronous resets/sets (see the simplification idiom and the Boxes
section for what to do here).

It is worth noting that in pure ``abc9`` mode, only the setup and arrival times
are passed to ABC9 (specifically, they are modelled as buffers with the given
delay). In ``abc9 -dff``, the flop itself is passed to ABC9, permitting
sequential optimisations.

Some vendors have universal DFF models which include async sets/resets even when
they're unused. Therefore *the simplification idiom* exists to handle this: by
using a ``techmap`` file to discover flops which have a constant driver to those
asynchronous controls, they can be mapped into an intermediate, simplified flop
which qualifies as an ``(* abc9_flop *)``, ran through :cmd:ref:`abc9`, and then
mapped back to the original flop. This is used in :cmd:ref:`synth_intel_alm` and
:cmd:ref:`synth_quicklogic` for the PolarPro3.

DFFs are usually specified to have setup constraints against the clock on the
input signals, and an arrival time for the ``Q`` output.

Boxes
^^^^^

A "box" is a purely-combinational piece of hard logic. If the logic is exposed
to ABC9, it's a "whitebox", otherwise it's a "blackbox". Carry chains would be
best implemented as whiteboxes, but a DSP would be best implemented as a
blackbox (multipliers are too complex to easily work with). LUT RAMs can be
implemented as whiteboxes too.

Boxes are arguably the biggest advantage that ABC9 has over ABC: by being aware
of carry chains and DSPs, it avoids optimising for a path that isn't the actual
critical path, while the generally-longer paths result in ABC9 being able to
reduce design area by mapping other logic to larger-but-slower cells.
