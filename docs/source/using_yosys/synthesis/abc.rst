The ABC toolbox
===============

.. role:: yoscrypt(code)
   :language: yoscrypt

ABC_, from the University of California, Berkeley, is a logic toolbox used for
fine-grained optimisation and LUT mapping.

Yosys has two different commands, which both use this logic toolbox, but use it
in different ways.

The `abc` pass can be used for both ASIC (e.g. :yoscrypt:`abc -liberty`) and
FPGA (:yoscrypt:`abc -lut`) mapping, but this page will focus on FPGA mapping.

The `abc9` pass generally provides superior mapping quality due to being aware
of combination boxes and DFF and LUT timings, giving it a more global view of
the mapping problem.

.. _ABC: https://github.com/berkeley-abc/abc

ABC: the unit delay model, simple and efficient
-----------------------------------------------

The `abc` pass uses a highly simplified view of an FPGA:

- An FPGA is made up of a network of inputs that connect through LUTs to a
  network of outputs. These inputs may actually be I/O pins, D flip-flops,
  memory blocks or DSPs, but ABC is unaware of this.
- Each LUT has 1 unit of delay between an input and its output, and this applies
  for all inputs of a LUT, and for all sizes of LUT up to the maximum LUT size
  allowed; e.g. the delay between the input of a LUT2 and its output is the same
  as the delay between the input of a LUT6 and its output.
- A LUT may take up a variable number of area units. This is constant for each
  size of LUT; e.g. a LUT4 may take up 1 unit of area, but a LUT5 may take up 2
  units of area, but this applies for all LUT4s and LUT5s.

This is known as the "unit delay model", because each LUT uses one unit of
delay.

From this view, the problem ABC has to solve is finding a mapping of the network
to LUTs that has the lowest delay, and then optimising the mapping for size
while maintaining this delay.

This approach has advantages:

- It is simple and easy to implement.
- Working with unit delays is fast to manipulate.
- It reflects *some* FPGA families, for example, the iCE40HX/LP fits the
  assumptions of the unit delay model quite well (almost all synchronous blocks,
  except for adders).

But this approach has drawbacks, too:

- The network of inputs and outputs with only LUTs means that a lot of
  combinational cells (multipliers and LUTRAM) are invisible to the unit delay
  model, meaning the critical path it optimises for is not necessarily the
  actual critical path.
- LUTs are implemented as multiplexer trees, so there is a delay caused by the
  result propagating through the remaining multiplexers. This means the
  assumption of delay being equal isn't true in physical hardware, and is
  proportionally larger for larger LUTs.
- Even synchronous blocks have arrival times (propagation delay between clock
  edge to output changing) and setup times (requirement for input to be stable
  before clock edge) which affect the delay of a path.

ABC9: the generalised delay model, realistic and flexible
---------------------------------------------------------

ABC9 uses a more detailed and accurate model of an FPGA:

- An FPGA is made up of a network of inputs that connect through LUTs and
  combinational boxes to a network of outputs. These boxes have specified delays
  between inputs and outputs, and may have an associated network ("white boxes")
  or not ("black boxes"), but must be treated as a whole.
- Each LUT has a specified delay between an input and its output in arbitrary
  delay units, and this varies for all inputs of a LUT and for all sizes of LUT,
  but each size of LUT has the same associated delay; e.g. the delay between
  input A and output is different between a LUT2 and a LUT6, but is constant for
  all LUT6s.
- A LUT may take up a variable number of area units. This is constant for each
  size of LUT; e.g. a LUT4 may take up 1 unit of area, but a LUT5 may take up 2
  units of area, but this applies for all LUT4s and LUT5s.

This is known as the "generalised delay model", because it has been generalised
to arbitrary delay units. ABC9 doesn't actually care what units you use here,
but the Yosys convention is picoseconds. Note the introduction of boxes as a
concept. While the generalised delay model does not require boxes, they
naturally fit into it to represent combinational delays. Even synchronous delays
like arrival and setup can be emulated with combinational boxes that act as a
delay. This is further extended to white boxes, where the mapper is able to see
inside a box, and remove orphan boxes with no outputs, such as adders.

Again, ABC9 finds a mapping of the network to LUTs that has the lowest delay,
and then minimises it to find the lowest area, but it has a lot more information
to work with about the network.

The result here is that ABC9 can remove boxes (like adders) to reduce area,
optimise better around those boxes, and also permute inputs to give the critical
path the fastest inputs.

.. todo:: more about logic minimization & register balancing et al with ABC

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
to `read_verilog` so that they aren't skipped.

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
zero (consider using `dfflegalize` to ensure this). - the DFF cannot have any
asynchronous resets/sets (see the simplification idiom and the Boxes section for
what to do here).

It is worth noting that in pure ``abc9`` mode, only the setup and arrival times
are passed to ABC9 (specifically, they are modelled as buffers with the given
delay). In ``abc9 -dff``, the flop itself is passed to ABC9, permitting
sequential optimisations.

Some vendors have universal DFF models which include async sets/resets even when
they're unused. Therefore *the simplification idiom* exists to handle this: by
using a ``techmap`` file to discover flops which have a constant driver to those
asynchronous controls, they can be mapped into an intermediate, simplified flop
which qualifies as an ``(* abc9_flop *)``, ran through `abc9`, and then mapped
back to the original flop. This is used in `synth_intel_alm` and
`synth_quicklogic` for the PolarPro3.

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
reduce design area by mapping other logic to slower cells with greater logic
density.

