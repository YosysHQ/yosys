.. _chapter:sota:

Evaluation of other OSS Verilog Synthesis Tools
===============================================

In this appendix [1]_ the existing FOSS Verilog synthesis tools [2]_ are
evaluated. Extremely limited or application specific tools (e.g. pure
Verilog Netlist parsers) as well as Verilog simulators are not included.
These existing solutions are tested using a set of representative
Verilog code snippets. It is shown that no existing FOSS tool implements
even close to a sufficient subset of Verilog to be usable as synthesis
tool for a wide range existing Verilog code.

The packages evaluated are:

-  Icarus Verilog  [3]_

-  Verilog-to-Routing (VTR) / Odin-II
   :cite:p:`vtr2012}`:raw-latex:`\cite{Odin`

-  HDL Analyzer and Netlist Architect (HANA)

-  Verilog front-end to VIS (vl2mv) :cite:p:`Cheng93vl2mv:a`

In each of the following sections Verilog modules that test a certain
Verilog language feature are presented and the support for these
features is tested in all the tools mentioned above. It is evaluated
whether the tools under test successfully generate netlists for the
Verilog input and whether these netlists match the simulation behavior
of the designs using testbenches.

All test cases are verified to be synthesizeable using Xilinx XST from
the Xilinx WebPACK suite.

Trivial features such as support for simple structural Verilog are not
explicitly tested.

Vl2mv and Odin-II generate output in the BLIF (Berkeley Logic
Interchange Format) and BLIF-MV (an extended version of BLIF) formats
respectively. ABC is used to convert this output to Verilog for
verification using testbenches.

Icarus Verilog generates EDIF (Electronic Design Interchange Format)
output utilizing LPM (Library of Parameterized Modules) cells. The EDIF
files are converted to Verilog using edif2ngd and netgen from Xilinx
WebPACK. A hand-written implementation of the LPM cells utilized by the
generated netlists is used for verification.

Following these functional tests, a quick analysis of the extensibility
of the tools under test is provided in a separate section.

The last section of this chapter finally concludes these series of
evaluations with a summary of the results.

.. code:: verilog
   :number-lines:

   module uut_always01(clock,
   		reset, count);

   input clock, reset;
   output [3:0] count;
   reg [3:0] count;

   always @(posedge clock)
   	count <= reset ?
   		0 : count + 1;



   endmodule

.. code:: verilog

   module uut_always02(clock,
   		reset, count);

   input clock, reset;
   output [3:0] count;
   reg [3:0] count;

   always @(posedge clock) begin
   	count <= count + 1;
   	if (reset)
   		count <= 0;
   end

   endmodule

[fig:StateOfTheArt_always12]

.. code:: verilog
   :number-lines:

   module uut_always03(clock, in1, in2, in3, in4, in5, in6, in7,
   		out1, out2, out3);

   input clock, in1, in2, in3, in4, in5, in6, in7;
   output out1, out2, out3;
   reg out1, out2, out3;

   always @(posedge clock) begin
   	out1 = in1;
   	if (in2)
   		out1 = !out1;
   	out2 <= out1;
   	if (in3)
   		out2 <= out2;
   	if (in4)
   		if (in5)
   			out3 <= in6;
   		else
   			out3 <= in7;
   	out1 = out1 ^ out2;
   end

   endmodule

[fig:StateOfTheArt_always3]

.. _sec:blocking_nonblocking:

Always blocks and blocking vs. nonblocking assignments
------------------------------------------------------

The "always"-block is one of the most fundamental non-trivial Verilog
language features. It can be used to model a combinatorial path (with
optional registers on the outputs) in a way that mimics a regular
programming language.

Within an always block, if- and case-statements can be used to model
multiplexers. Blocking assignments (:math:`=`) and nonblocking
assignments (:math:`<=`) are used to populate the leaf-nodes of these
multiplexer trees. Unassigned leaf-nodes default to feedback paths that
cause the output register to hold the previous value. More advanced
synthesis tools often convert these feedback paths to register enable
signals or even generate circuits with clock gating.

Registers assigned with nonblocking assignments (:math:`<=`) behave
differently from variables in regular programming languages: In a
simulation they are not updated immediately after being assigned.
Instead the right-hand sides are evaluated and the results stored in
temporary memory locations. After all pending updates have been prepared
in this way they are executed, thus yielding semi-parallel execution of
all nonblocking assignments.

For synthesis this means that every occurrence of that register in an
expression addresses the output port of the corresponding register
regardless of the question whether the register has been assigned a new
value in an earlier command in the same always block. Therefore with
nonblocking assignments the order of the assignments has no effect on
the resulting circuit as long as the left-hand sides of the assignments
are unique.

The three example codes in
:numref:`Fig. %s <fig:StateOfTheArt_always12>`
and :numref:`Fig. %s <fig:StateOfTheArt_always3>`
use all these features and can thus be used to test the synthesis tools
capabilities to synthesize always blocks correctly.

The first example is only using the most fundamental Verilog features.
All tools under test were able to successfully synthesize this design.

.. code:: verilog
   :number-lines:

   module uut_arrays01(clock, we, addr, wr_data, rd_data);

   input clock, we;
   input [3:0] addr, wr_data;
   output [3:0] rd_data;
   reg [3:0] rd_data;

   reg [3:0] memory [15:0];

   always @(posedge clock) begin
   	if (we)
   		memory[addr] <= wr_data;
   	rd_data <= memory[addr];
   end

   endmodule

[fig:StateOfTheArt_arrays]

The 2nd example is functionally identical to the 1st one but is using an
if-statement inside the always block. Odin-II fails to synthesize it and
instead produces the following error message:

::

   ERROR: (File: always02.v) (Line number: 13)
   You've defined the driver "count~0" twice

Vl2mv does not produce an error message but outputs an invalid synthesis
result that is not using the reset input at all.

Icarus Verilog also doesn't produce an error message but generates an
invalid output for this 2nd example. The code generated by Icarus
Verilog only implements the reset path for the count register,
effectively setting the output to constant 0.

So of all tools under test only HANA was able to create correct
synthesis results for the 2nd example.

The 3rd example is using blocking and nonblocking assignments and many
if statements. Odin also fails to synthesize this example:

::

   ERROR: (File: always03.v) (Line number: 8)
   ODIN doesn't handle blocking statements in Sequential blocks

HANA, Icarus Verilog and vl2mv create invalid synthesis results for the
3rd example.

So unfortunately none of the tools under test provide a complete and
correct implementation of blocking and nonblocking assignments.

Arrays for memory modelling
---------------------------

Verilog arrays are part of the synthesizeable subset of Verilog and are
commonly used to model addressable memory. The Verilog code in
:numref:`Fig. %s <fig:StateOfTheArt_arrays>`
demonstrates this by implementing a single port memory.

For this design HANA, vl2m and ODIN-II generate error messages
indicating that arrays are not supported.

.. code:: verilog
   :number-lines:

   module uut_forgen01(a, y);

   input [4:0] a;
   output y;

   integer i, j;
   reg [31:0] lut;

   initial begin
   	for (i = 0; i < 32; i = i+1) begin
   		lut[i] = i > 1;
   		for (j = 2; j*j <= i; j = j+1)
   			if (i % j == 0)
   				lut[i] = 0;
   	end
   end

   assign y = lut[a];

   endmodule

[fig:StateOfTheArt_for]

Icarus Verilog produces an invalid output that is using the address only
for reads. Instead of using the address input for writes, the generated
design simply loads the data to all memory locations whenever the
write-enable input is active, effectively turning the design into a
single 4-bit D-Flip-Flop with enable input.

As all tools under test already fail this simple test, there is nothing
to gain by continuing tests on this aspect of Verilog synthesis such as
synthesis of dual port memories, correct handling of write collisions,
and so forth.

.. code:: verilog
   :number-lines:

   module uut_forgen02(a, b, cin, y, cout);

   parameter WIDTH = 8;

   input [WIDTH-1:0] a, b;
   input cin;

   output [WIDTH-1:0] y;
   output cout;

   genvar i;
   wire [WIDTH-1:0] carry;

   generate
   	for (i = 0; i < WIDTH; i=i+1) begin:adder
   		wire [2:0] D;
   		assign D[1:0] = { a[i], b[i] };
   		if (i == 0) begin:chain
   			assign D[2] = cin;
   		end else begin:chain
   			assign D[2] = carry[i-1];
   		end
   		assign y[i] = ^D;
   		assign carry[i] = &D[1:0] | (^D[1:0] & D[2]);
   	end
   endgenerate

   assign cout = carry[WIDTH-1];

   endmodule

[fig:StateOfTheArt_gen]

For-loops and generate blocks
-----------------------------

For-loops and generate blocks are more advanced Verilog features. These
features allow the circuit designer to add program code to her design
that is evaluated during synthesis to generate (parts of) the circuits
description; something that could only be done using a code generator
otherwise.

For-loops are only allowed in synthesizeable Verilog if they can be
completely unrolled. Then they can be a powerful tool to generate array
logic or static lookup tables. The code in
:numref:`Fig. %s <fig:StateOfTheArt_for>` generates a
circuit that tests a 5 bit value for being a prime number using a static
lookup table.

Generate blocks can be used to model array logic in complex parametric
designs. The code in
:numref:`Fig. %s <fig:StateOfTheArt_gen>` implements a
ripple-carry adder with parametric width from simple assign-statements
and logic operations using a Verilog generate block.

All tools under test failed to synthesize both test cases. HANA creates
invalid output in both cases. Icarus Verilog creates invalid output for
the first test and fails with an error for the second case. The other
two tools fail with error messages for both tests.

Extensibility
-------------

This section briefly discusses the extensibility of the tools under test
and their internal data- and control-flow. As all tools under test
already failed to synthesize simple Verilog always-blocks correctly, not
much resources have been spent on evaluating the extensibility of these
tools and therefore only a very brief discussion of the topic is
provided here.

HANA synthesizes for a built-in library of standard cells using two
passes over an AST representation of the Verilog input. This approach
executes fast but limits the extensibility as everything happens in only
two comparable complex AST walks and there is no universal intermediate
representation that is flexible enough to be used in arbitrary
optimizations.

Odin-II and vl2m are both front ends to existing synthesis flows. As
such they only try to quickly convert the Verilog input into the
internal representation of their respective flows (BLIF). So
extensibility is less of an issue here as potential extensions would
likely be implemented in other components of the flow.

Icarus Verilog is clearly designed to be a simulation tool rather than a
synthesis tool. The synthesis part of Icarus Verilog is an ad-hoc add-on
to Icarus Verilog that aims at converting an internal representation
that is meant for generation of a virtual machine based simulation code
to netlists.

Summary and Outlook
-------------------

Table \ :numref:`tab:StateOfTheArt_sum` summarizes
the tests performed. Clearly none of the tools under test make a serious
attempt at providing a feature-complete implementation of Verilog. It
can be argued that Odin-II performed best in the test as it never
generated incorrect code but instead produced error messages indicating
that unsupported Verilog features where used in the Verilog input.

In conclusion, to the best knowledge of the author, there is no FOSS
Verilog synthesis tool other than Yosys that is anywhere near feature
completeness and therefore there is no other candidate for a generic
Verilog front end and/or synthesis framework to be used as a basis for
custom synthesis tools.

Yosys could also replace vl2m and/or Odin-II in their respective flows
or function as a pre-compiler that can translate full-featured Verilog
code to the simple subset of Verilog that is understood by vl2m and
Odin-II.

Yosys is designed for extensibility. It can be used as-is to synthesize
Verilog code to netlists, but its main purpose is to be used as basis
for custom tools. Yosys is structured in a language dependent Verilog
front end and language independent synthesis code (which is in itself
structured in independent passes). This architecture will simplify
implementing additional HDL front ends and/or additional synthesis
passes.

Chapter \ :numref:`<CHAPTER_eval>` contains a more detailed
evaluation of Yosys using real-world designs that are far out of reach
for any of the other tools discussed in this appendix.

…passed 2em …produced error 2em :math:`\skull` …incorrect output

[tab:StateOfTheArt_sum]

.. [1]
   This appendix is an updated version of an unpublished student
   research paper. :cite:p:`VerilogFossEval`

.. [2]
   To the author's best knowledge, all relevant tools that existed at
   the time of this writing are included. But as there is no formal
   channel through which such tools are published it is hard to give any
   guarantees in that matter.

.. [3]
   Icarus Verilog is mainly a simulation tool but also supported
   synthesis up to version 0.8. Therefore version 0.8.7 is used for this
   evaluation.)
