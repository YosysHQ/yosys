.. _chapter:overview:

Implementation overview
=======================

Yosys is an extensible open source hardware synthesis tool. It is aimed at
designers who are looking for an easily accessible, universal, and
vendor-independent synthesis tool, as well as scientists who do research in
electronic design automation (EDA) and are looking for an open synthesis
framework that can be used to test algorithms on complex real-world designs.

Yosys can synthesize a large subset of Verilog 2005 and has been tested with a
wide range of real-world designs, including the `OpenRISC 1200 CPU`_, the
`openMSP430 CPU`_, the `OpenCores I2C master`_, and the `k68 CPU`_.

.. _OpenRISC 1200 CPU: https://github.com/openrisc/or1200

.. _openMSP430 CPU: http://opencores.org/projects/openmsp430

.. _OpenCores I2C master: http://opencores.org/projects/i2c

.. _k68 CPU: http://opencores.org/projects/k68

As of this writing a Yosys VHDL frontend is in development.

Yosys is written in C++ (using some features from the new C++11 standard). This
chapter describes some of the fundamental Yosys data structures. For the sake of
simplicity the C++ type names used in the Yosys implementation are used in this
chapter, even though the chapter only explains the conceptual idea behind it and
can be used as reference to implement a similar system in any language.

Simplified data flow
--------------------

:numref:`Figure %s <fig:Overview_flow>` shows the simplified data flow within
Yosys. Rectangles in the figure represent program modules and ellipses internal
data structures that are used to exchange design data between the program
modules.

Design data is read in using one of the frontend modules. The high-level HDL
frontends for Verilog and VHDL code generate an abstract syntax tree (AST) that
is then passed to the AST frontend. Note that both HDL frontends use the same
AST representation that is powerful enough to cover the Verilog HDL and VHDL
language.

The AST Frontend then compiles the AST to Yosys's main internal data format, the
RTL Intermediate Language (RTLIL). A more detailed description of this format is
given in the next section.

There is also a text representation of the RTLIL data structure that can be
parsed using the RTLIL Frontend.

The design data may then be transformed using a series of passes that all
operate on the RTLIL representation of the design.

Finally the design in RTLIL representation is converted back to text by one of
the backends, namely the Verilog Backend for generating Verilog netlists and the
RTLIL Backend for writing the RTLIL data in the same format that is understood
by the RTLIL Frontend.

With the exception of the AST Frontend, which is called by the high-level HDL
frontends and can't be called directly by the user, all program modules are
called by the user (usually using a synthesis script that contains text commands
for Yosys).

By combining passes in different ways and/or adding additional passes to Yosys
it is possible to adapt Yosys to a wide range of applications. For this to be
possible it is key that (1) all passes operate on the same data structure
(RTLIL) and (2) that this data structure is powerful enough to represent the
design in different stages of the synthesis.

.. figure:: ../images/overview_flow.*
	:class: width-helper
	:name: fig:Overview_flow

	Yosys simplified data flow (ellipses: data structures, rectangles:
	program modules)

The RTL Intermediate Language (RTLIL)
-------------------------------------

All frontends, passes and backends in Yosys operate on a design in RTLIL
representation. The only exception are the high-level frontends that use the AST
representation as an intermediate step before generating RTLIL data.

In order to avoid reinventing names for the RTLIL classes, they are simply
referred to by their full C++ name, i.e. including the RTLIL:: namespace prefix,
in this document.

:numref:`Figure %s <fig:Overview_RTLIL>` shows a simplified Entity-Relationship
Diagram (ER Diagram) of RTLIL. In :math:`1:N` relationships the arrow points
from the :math:`N` side to the :math:`1`. For example one RTLIL::Design contains
:math:`N` (zero to many) instances of RTLIL::Module. A two-pointed arrow
indicates a :math:`1:1` relationship.

The RTLIL::Design is the root object of the RTLIL data structure. There is
always one "current design" in memory which passes operate on, frontends add
data to and backends convert to exportable formats. But in some cases passes
internally generate additional RTLIL::Design objects. For example when a pass is
reading an auxiliary Verilog file such as a cell library, it might create an
additional RTLIL::Design object and call the Verilog frontend with this other
object to parse the cell library.

.. figure:: ../images/overview_rtlil.*
	:class: width-helper
	:name: fig:Overview_RTLIL

	Simplified RTLIL Entity-Relationship Diagram

There is only one active RTLIL::Design object that is used by all frontends,
passes and backends called by the user, e.g. using a synthesis script. The
RTLIL::Design then contains zero to many RTLIL::Module objects. This corresponds
to modules in Verilog or entities in VHDL. Each module in turn contains objects
from three different categories:

-  RTLIL::Cell and RTLIL::Wire objects represent classical netlist data.

-  RTLIL::Process objects represent the decision trees (if-then-else statements,
   etc.) and synchronization declarations (clock signals and sensitivity) from
   Verilog always and VHDL process blocks.

-  RTLIL::Memory objects represent addressable memories (arrays).

Usually the output of the synthesis procedure is a netlist, i.e. all
RTLIL::Process and RTLIL::Memory objects must be replaced by RTLIL::Cell and
RTLIL::Wire objects by synthesis passes.

All features of the HDL that cannot be mapped directly to these RTLIL classes
must be transformed to an RTLIL-compatible representation by the HDL frontend.
This includes Verilog-features such as generate-blocks, loops and parameters.

The following sections contain a more detailed description of the different
parts of RTLIL and rationale behind some of the design decisions.

RTLIL identifiers
~~~~~~~~~~~~~~~~~

All identifiers in RTLIL (such as module names, port names, signal names, cell
types, etc.) follow the following naming convention: they must either start with
a backslash (\) or a dollar sign ($).

Identifiers starting with a backslash are public visible identifiers. Usually
they originate from one of the HDL input files. For example the signal name
"\\sig42" is most likely a signal that was declared using the name "sig42" in an
HDL input file. On the other hand the signal name "$sig42" is an auto-generated
signal name. The backends convert all identifiers that start with a dollar sign
to identifiers that do not collide with identifiers that start with a backslash.

This has three advantages:

-  First, it is impossible that an auto-generated identifier collides with an
   identifier that was provided by the user.

-  Second, the information about which identifiers were originally provided by
   the user is always available which can help guide some optimizations. For
   example the "opt_rmunused" tries to preserve signals with a user-provided
   name but doesn't hesitate to delete signals that have auto-generated names
   when they just duplicate other signals.

-  Third, the delicate job of finding suitable auto-generated public visible
   names is deferred to one central location. Internally auto-generated names
   that may hold important information for Yosys developers can be used without
   disturbing external tools. For example the Verilog backend assigns names in
   the form \_integer\_.

Whitespace and control characters (any character with an ASCII code 32 or less)
are not allowed in RTLIL identifiers; most frontends and backends cannot support
these characters in identifiers.

In order to avoid programming errors, the RTLIL data structures check if all
identifiers start with either a backslash or a dollar sign, and contain no
whitespace or control characters. Violating these rules results in a runtime
error.

All RTLIL identifiers are case sensitive.

Some transformations, such as flattening, may have to change identifiers
provided by the user to avoid name collisions. When that happens, attribute
"hdlname" is attached to the object with the changed identifier. This attribute
contains one name (if emitted directly by the frontend, or is a result of
disambiguation) or multiple names separated by spaces (if a result of
flattening). All names specified in the "hdlname" attribute are public and do
not include the leading "\".

RTLIL::Design and RTLIL::Module
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The RTLIL::Design object is basically just a container for RTLIL::Module
objects. In addition to a list of RTLIL::Module objects the RTLIL::Design also
keeps a list of selected objects, i.e. the objects that passes should operate
on. In most cases the whole design is selected and therefore passes operate on
the whole design. But this mechanism can be useful for more complex synthesis
jobs in which only parts of the design should be affected by certain passes.

Besides the objects shown in the ER diagram in :numref:`Fig. %s
<fig:Overview_RTLIL>` an RTLIL::Module object contains the following additional
properties:

-  The module name
-  A list of attributes
-  A list of connections between wires
-  An optional frontend callback used to derive parametrized variations of the
   module

The attributes can be Verilog attributes imported by the Verilog frontend or
attributes assigned by passes. They can be used to store additional metadata
about modules or just mark them to be used by certain part of the synthesis
script but not by others.

Verilog and VHDL both support parametric modules (known as "generic entities" in
VHDL). The RTLIL format does not support parametric modules itself. Instead each
module contains a callback function into the AST frontend to generate a
parametrized variation of the RTLIL::Module as needed. This callback then
returns the auto-generated name of the parametrized variation of the module. (A
hash over the parameters and the module name is used to prohibit the same
parametrized variation from being generated twice. For modules with only a few
parameters, a name directly containing all parameters is generated instead of a
hash string.)

.. _sec:rtlil_cell_wire:

RTLIL::Cell and RTLIL::Wire
~~~~~~~~~~~~~~~~~~~~~~~~~~~

A module contains zero to many RTLIL::Cell and RTLIL::Wire objects. Objects of
these types are used to model netlists. Usually the goal of all synthesis
efforts is to convert all modules to a state where the functionality of the
module is implemented only by cells from a given cell library and wires to
connect these cells with each other. Note that module ports are just wires with
a special property.

An RTLIL::Wire object has the following properties:

-  The wire name
-  A list of attributes
-  A width (buses are just wires with a width > 1)
-  Bus direction (MSB to LSB or vice versa)
-  Lowest valid bit index (LSB or MSB depending on bus direction)
-  If the wire is a port: port number and direction (input/output/inout)

As with modules, the attributes can be Verilog attributes imported by the
Verilog frontend or attributes assigned by passes.

In Yosys, busses (signal vectors) are represented using a single wire object
with a width > 1. So Yosys does not convert signal vectors to individual
signals. This makes some aspects of RTLIL more complex but enables Yosys to be
used for coarse grain synthesis where the cells of the target architecture
operate on entire signal vectors instead of single bit wires.

In Verilog and VHDL, busses may have arbitrary bounds, and LSB can have either
the lowest or the highest bit index. In RTLIL, bit 0 always corresponds to LSB;
however, information from the HDL frontend is preserved so that the bus will be
correctly indexed in error messages, backend output, constraint files, etc.

An RTLIL::Cell object has the following properties:

-  The cell name and type
-  A list of attributes
-  A list of parameters (for parametric cells)
-  Cell ports and the connections of ports to wires and constants

The connections of ports to wires are coded by assigning an RTLIL::SigSpec to
each cell port. The RTLIL::SigSpec data type is described in the next section.

.. _sec:rtlil_sigspec:

RTLIL::SigSpec
~~~~~~~~~~~~~~

A "signal" is everything that can be applied to a cell port. I.e.

-  | Any constant value of arbitrary bit-width
   | 1em For example: ``1337, 16'b0000010100111001, 1'b1, 1'bx``

-  | All bits of a wire or a selection of bits from a wire
   | 1em For example: ``mywire, mywire[24], mywire[15:8]``

-  | Concatenations of the above
   | 1em For example: ``{16'd1337, mywire[15:8]}``

The RTLIL::SigSpec data type is used to represent signals. The RTLIL::Cell
object contains one RTLIL::SigSpec for each cell port.

In addition, connections between wires are represented using a pair of
RTLIL::SigSpec objects. Such pairs are needed in different locations. Therefore
the type name RTLIL::SigSig was defined for such a pair.

.. _sec:rtlil_process:

RTLIL::Process
~~~~~~~~~~~~~~

When a high-level HDL frontend processes behavioural code it splits it up into
data path logic (e.g. the expression a + b is replaced by the output of an adder
that takes a and b as inputs) and an RTLIL::Process that models the control
logic of the behavioural code. Let's consider a simple example:

.. code:: verilog
   :number-lines:

   module ff_with_en_and_async_reset(clock, reset, enable, d, q);
   input clock, reset, enable, d;
   output reg q;
   always @(posedge clock, posedge reset)
       if (reset)
           q <= 0;
       else if (enable)
           q <= d;
   endmodule

In this example there is no data path and therefore the RTLIL::Module generated
by the frontend only contains a few RTLIL::Wire objects and an RTLIL::Process.
The RTLIL::Process in RTLIL syntax:

.. code:: RTLIL
   :number-lines:

   process $proc$ff_with_en_and_async_reset.v:4$1
       assign $0\q[0:0] \q
       switch \reset
           case 1'1
               assign $0\q[0:0] 1'0
           case
               switch \enable
                   case 1'1
                       assign $0\q[0:0] \d
                   case
               end
       end
       sync posedge \clock
           update \q $0\q[0:0]
       sync posedge \reset
           update \q $0\q[0:0]
   end

This RTLIL::Process contains two RTLIL::SyncRule objects, two RTLIL::SwitchRule
objects and five RTLIL::CaseRule objects. The wire $0\q[0:0] is an automatically
created wire that holds the next value of \\q. The lines :math:`2 \dots 12`
describe how $0\q[0:0] should be calculated. The lines :math:`13 \dots 16`
describe how the value of $0\q[0:0] is used to update \\q.

An RTLIL::Process is a container for zero or more RTLIL::SyncRule objects and
exactly one RTLIL::CaseRule object, which is called the root case.

An RTLIL::SyncRule object contains an (optional) synchronization condition
(signal and edge-type), zero or more assignments (RTLIL::SigSig), and zero or
more memory writes (RTLIL::MemWriteAction). The always synchronization condition
is used to break combinatorial loops when a latch should be inferred instead.

An RTLIL::CaseRule is a container for zero or more assignments (RTLIL::SigSig)
and zero or more RTLIL::SwitchRule objects. An RTLIL::SwitchRule objects is a
container for zero or more RTLIL::CaseRule objects.

In the above example the lines :math:`2 \dots 12` are the root case. Here
$0\q[0:0] is first assigned the old value \\q as default value (line 2). The
root case also contains an RTLIL::SwitchRule object (lines :math:`3 \dots 12`).
Such an object is very similar to the C switch statement as it uses a control
signal (\\reset in this case) to determine which of its cases should be active.
The RTLIL::SwitchRule object then contains one RTLIL::CaseRule object per case.
In this example there is a case [1]_ for \\reset == 1 that causes $0\q[0:0] to
be set (lines 4 and 5) and a default case that in turn contains a switch that
sets $0\q[0:0] to the value of \\d if \\enable is active (lines :math:`6 \dots
11`).

A case can specify zero or more compare values that will determine whether it
matches. Each of the compare values must be the exact same width as the control
signal. When more than one compare value is specified, the case matches if any
of them matches the control signal; when zero compare values are specified, the
case always matches (i.e. it is the default case).

A switch prioritizes cases from first to last: multiple cases can match, but
only the first matched case becomes active. This normally synthesizes to a
priority encoder. The parallel_case attribute allows passes to assume that no
more than one case will match, and full_case attribute allows passes to assume
that exactly one case will match; if these invariants are ever dynamically
violated, the behavior is undefined. These attributes are useful when an
invariant invisible to the synthesizer causes the control signal to never take
certain bit patterns.

The lines :math:`13 \dots 16` then cause \\q to be updated whenever there is a
positive clock edge on \\clock or \\reset.

In order to generate such a representation, the language frontend must be able
to handle blocking and nonblocking assignments correctly. However, the language
frontend does not need to identify the correct type of storage element for the
output signal or generate multiplexers for the decision tree. This is done by
passes that work on the RTLIL representation. Therefore it is relatively easy to
substitute these steps with other algorithms that target different target
architectures or perform optimizations or other transformations on the decision
trees before further processing them.

One of the first actions performed on a design in RTLIL representation in most
synthesis scripts is identifying asynchronous resets. This is usually done using
the proc_arst pass. This pass transforms the above example to the following
RTLIL::Process:

.. code:: RTLIL
   :number-lines:

   process $proc$ff_with_en_and_async_reset.v:4$1
       assign $0\q[0:0] \q
       switch \enable
           case 1'1
               assign $0\q[0:0] \d
           case
       end
       sync posedge \clock
           update \q $0\q[0:0]
       sync high \reset
           update \q 1'0
   end

This pass has transformed the outer RTLIL::SwitchRule into a modified
RTLIL::SyncRule object for the \\reset signal. Further processing converts the
RTLIL::Process into e.g. a d-type flip-flop with asynchronous reset and a
multiplexer for the enable signal:

.. code:: RTLIL
   :number-lines:

   cell $adff $procdff$6
       parameter \ARST_POLARITY 1'1
       parameter \ARST_VALUE 1'0
       parameter \CLK_POLARITY 1'1
       parameter \WIDTH 1
       connect \ARST \reset
       connect \CLK \clock
       connect \D $0\q[0:0]
       connect \Q \q
   end
   cell $mux $procmux$3
       parameter \WIDTH 1
       connect \A \q
       connect \B \d
       connect \S \enable
       connect \Y $0\q[0:0]
   end

Different combinations of passes may yield different results. Note that $adff
and $mux are internal cell types that still need to be mapped to cell types from
the target cell library.

Some passes refuse to operate on modules that still contain RTLIL::Process
objects as the presence of these objects in a module increases the complexity.
Therefore the passes to translate processes to a netlist of cells are usually
called early in a synthesis script. The proc pass calls a series of other passes
that together perform this conversion in a way that is suitable for most
synthesis tasks.

.. _sec:rtlil_memory:

RTLIL::Memory
~~~~~~~~~~~~~

For every array (memory) in the HDL code an RTLIL::Memory object is created. A
memory object has the following properties:

-  The memory name
-  A list of attributes
-  The width of an addressable word
-  The size of the memory in number of words

All read accesses to the memory are transformed to $memrd cells and all write
accesses to $memwr cells by the language frontend. These cells consist of
independent read- and write-ports to the memory. Memory initialization is
transformed to $meminit cells by the language frontend. The ``\MEMID`` parameter
on these cells is used to link them together and to the RTLIL::Memory object
they belong to.

The rationale behind using separate cells for the individual ports versus
creating a large multiport memory cell right in the language frontend is that
the separate $memrd and $memwr cells can be consolidated using resource sharing.
As resource sharing is a non-trivial optimization problem where different
synthesis tasks can have different requirements it lends itself to do the
optimisation in separate passes and merge the RTLIL::Memory objects and $memrd
and $memwr cells to multiport memory blocks after resource sharing is completed.

The memory pass performs this conversion and can (depending on the options
passed to it) transform the memories directly to d-type flip-flops and address
logic or yield multiport memory blocks (represented using $mem cells).

See :numref:`Sec. %s <sec:memcells>` for details about the memory cell types.

Command interface and synthesis scripts
---------------------------------------

Yosys reads and processes commands from synthesis scripts, command line
arguments and an interactive command prompt. Yosys commands consist of a command
name and an optional whitespace separated list of arguments. Commands are
terminated using the newline character or a semicolon (;). Empty lines and lines
starting with the hash sign (#) are ignored. See :numref:`Sec. %s
<sec:typusecase>` for an example synthesis script.

The command help can be used to access the command reference manual.

Most commands can operate not only on the entire design but also specifically on
selected parts of the design. For example the command dump will print all
selected objects in the current design while dump foobar will only print the
module foobar and dump \* will print the entire design regardless of the current
selection.

.. code:: yoscrypt

	dump */t:$add %x:+[A] \*/w:\* %i

The selection mechanism is very powerful. For example the command above will
print all wires that are connected to the ``\A`` port of a ``$add`` cell.
Detailed documentation of the select framework can be found in the command
reference for the ``select`` command.

Source tree and build system
----------------------------

The Yosys source tree is organized into the following top-level
directories:

-  | backends/
   | This directory contains a subdirectory for each of the backend modules.

-  | frontends/
   | This directory contains a subdirectory for each of the frontend modules.

-  | kernel/
   | This directory contains all the core functionality of Yosys. This includes
     the functions and definitions for working with the RTLIL data structures
     (rtlil.h and rtlil.cc), the main() function (driver.cc), the internal
     framework for generating log messages (log.h and log.cc), the internal
     framework for registering and calling passes (register.h and register.cc),
     some core commands that are not really passes (select.cc, show.cc, …) and a
     couple of other small utility libraries.

-  | passes/
   | This directory contains a subdirectory for each pass or group of passes.
     For example as of this writing the directory passes/opt/ contains the code
     for seven passes: opt, opt_expr, opt_muxtree, opt_reduce, opt_rmdff,
     opt_rmunused and opt_merge.

-  | techlibs/
   | This directory contains simulation models and standard implementations for
     the cells from the internal cell library.

-  | tests/
   | This directory contains a couple of test cases. Most of the smaller tests
     are executed automatically when make test is called. The larger tests must
     be executed manually. Most of the larger tests require downloading external
     HDL source code and/or external tools. The tests range from comparing
     simulation results of the synthesized design to the original sources to
     logic equivalence checking of entire CPU cores.

The top-level Makefile includes frontends/\*/Makefile.inc,
passes/\*/Makefile.inc and backends/\*/Makefile.inc. So when extending Yosys it
is enough to create a new directory in frontends/, passes/ or backends/ with
your sources and a Makefile.inc. The Yosys kernel automatically detects all
commands linked with Yosys. So it is not needed to add additional commands to a
central list of commands.

Good starting points for reading example source code to learn how to write
passes are passes/opt/opt_rmdff.cc and passes/opt/opt_merge.cc.

See the top-level README file for a quick Getting Started guide and build
instructions. The Yosys build is based solely on Makefiles.

Users of the Qt Creator IDE can generate a QT Creator project file using make
qtcreator. Users of the Eclipse IDE can use the "Makefile Project with Existing
Code" project type in the Eclipse "New Project" dialog (only available after the
CDT plugin has been installed) to create an Eclipse project in order to
programming extensions to Yosys or just browse the Yosys code base.

.. [1]
   The syntax 1'1 in the RTLIL code specifies a constant with a length of one
   bit (the first "1"), and this bit is a one (the second "1").
