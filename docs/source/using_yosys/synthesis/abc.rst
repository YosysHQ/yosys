The ABC toolbox
---------------

.. role:: yoscrypt(code)
   :language: yoscrypt

ABC_, from the University of California, Berkeley, is a logic toolbox used for
fine-grained optimisation and LUT mapping.

Yosys has two different commands, which both use this logic toolbox, but use it
in different ways.

The :cmd:ref:`abc` pass can be used for both ASIC (e.g. :yoscrypt:`abc
-liberty`) and FPGA (:yoscrypt:`abc -lut`) mapping, but this page will focus on
FPGA mapping.

The :cmd:ref:`abc9` pass generally provides superior mapping quality due to
being aware of combination boxes and DFF and LUT timings, giving it a more
global view of the mapping problem.

.. _ABC: https://github.com/berkeley-abc/abc

ABC: the unit delay model, simple and efficient
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The :cmd:ref:`abc` pass uses a highly simplified view of an FPGA:

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
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

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
