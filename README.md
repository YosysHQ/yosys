```
yosys -- Yosys Open SYnthesis Suite

Copyright (C) 2012 - 2019  Clifford Wolf <clifford@clifford.at>

Permission to use, copy, modify, and/or distribute this software for any
purpose with or without fee is hereby granted, provided that the above
copyright notice and this permission notice appear in all copies.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
```


yosys – Yosys Open SYnthesis Suite
===================================

This is a framework for RTL synthesis tools. It currently has
extensive Verilog-2005 support and provides a basic set of
synthesis algorithms for various application domains.

Yosys can be adapted to perform any synthesis job by combining
the existing passes (algorithms) using synthesis scripts and
adding additional passes as needed by extending the yosys C++
code base.

Yosys is free software licensed under the ISC license (a GPL
compatible license that is similar in terms to the MIT license
or the 2-clause BSD license).


Web Site and Other Resources
============================

More information and documentation can be found on the Yosys web site:
- http://www.clifford.at/yosys/

The "Documentation" page on the web site contains links to more resources,
including a manual that even describes some of the Yosys internals:
- http://www.clifford.at/yosys/documentation.html

The file `CodingReadme` in this directory contains additional information
for people interested in using the Yosys C++ APIs.

Users interested in formal verification might want to use the formal verification
front-end for Yosys, SymbiYosys:
- https://symbiyosys.readthedocs.io/en/latest/
- https://github.com/YosysHQ/SymbiYosys


Setup
======

You need a C++ compiler with C++11 support (up-to-date CLANG or GCC is
recommended) and some standard tools such as GNU Flex, GNU Bison, and GNU Make.
TCL, readline and libffi are optional (see ``ENABLE_*`` settings in Makefile).
Xdot (graphviz) is used by the ``show`` command in yosys to display schematics.

For example on Ubuntu Linux 16.04 LTS the following commands will install all
prerequisites for building yosys:

	$ sudo apt-get install build-essential clang bison flex \
		libreadline-dev gawk tcl-dev libffi-dev git \
		graphviz xdot pkg-config python3 libboost-system-dev \
		libboost-python-dev libboost-filesystem-dev zlib1g-dev

Similarily, on Mac OS X Homebrew can be used to install dependencies:

	$ brew tap Homebrew/bundle && brew bundle

or MacPorts:

	$ sudo port install bison flex readline gawk libffi \
		git graphviz pkgconfig python36 boost zlib tcl

On FreeBSD use the following command to install all prerequisites:

	# pkg install bison flex readline gawk libffi\
		git graphviz pkgconf python3 python36 tcl-wrapper boost-libs

On FreeBSD system use gmake instead of make. To run tests use:
    % MAKE=gmake CC=cc gmake test

For Cygwin use the following command to install all prerequisites, or select these additional packages:

	setup-x86_64.exe -q --packages=bison,flex,gcc-core,gcc-g++,git,libffi-devel,libreadline-devel,make,pkg-config,python3,tcl-devel,boost-build,zlib-devel

There are also pre-compiled Yosys binary packages for Ubuntu and Win32 as well
as a source distribution for Visual Studio. Visit the Yosys download page for
more information: http://www.clifford.at/yosys/download.html

To configure the build system to use a specific compiler, use one of

	$ make config-clang
	$ make config-gcc

For other compilers and build configurations it might be
necessary to make some changes to the config section of the
Makefile.

	$ vi Makefile            # ..or..
	$ vi Makefile.conf

To build Yosys simply type 'make' in this directory.

	$ make
	$ sudo make install

Note that this also downloads, builds and installs ABC (using yosys-abc
as executable name).

Tests are located in the tests subdirectory and can be executed using the test target. Note that you need gawk as well as a recent version of iverilog (i.e. build from git). Then, execute tests via:

	$ make test

Getting Started
===============

Yosys can be used with the interactive command shell, with
synthesis scripts or with command line arguments. Let's perform
a simple synthesis job using the interactive command shell:

	$ ./yosys
	yosys>

the command ``help`` can be used to print a list of all available
commands and ``help <command>`` to print details on the specified command:

	yosys> help help

reading and elaborating the design using the Verilog frontend:

	yosys> read -sv tests/simple/fiedler-cooley.v
	yosys> hierarchy -top up3down5

writing the design to the console in Yosys's internal format:

	yosys> write_ilang

convert processes (``always`` blocks) to netlist elements and perform
some simple optimizations:

	yosys> proc; opt

display design netlist using ``xdot``:

	yosys> show

the same thing using ``gv`` as postscript viewer:

	yosys> show -format ps -viewer gv

translating netlist to gate logic and perform some simple optimizations:

	yosys> techmap; opt

write design netlist to a new Verilog file:

	yosys> write_verilog synth.v

or using a simple synthesis script:

	$ cat synth.ys
	read -sv tests/simple/fiedler-cooley.v
	hierarchy -top up3down5
	proc; opt; techmap; opt
	write_verilog synth.v

	$ ./yosys synth.ys

If ABC is enabled in the Yosys build configuration and a cell library is given
in the liberty file ``mycells.lib``, the following synthesis script will
synthesize for the given cell library:

	# read design
	read -sv tests/simple/fiedler-cooley.v
	hierarchy -top up3down5

	# the high-level stuff
	proc; fsm; opt; memory; opt

	# mapping to internal cell library
	techmap; opt

	# mapping flip-flops to mycells.lib
	dfflibmap -liberty mycells.lib

	# mapping logic to mycells.lib
	abc -liberty mycells.lib

	# cleanup
	clean

If you do not have a liberty file but want to test this synthesis script,
you can use the file ``examples/cmos/cmos_cells.lib`` from the yosys sources
as simple example.

Liberty file downloads for and information about free and open ASIC standard
cell libraries can be found here:

- http://www.vlsitechnology.org/html/libraries.html
- http://www.vlsitechnology.org/synopsys/vsclib013.lib

The command ``synth`` provides a good default synthesis script (see
``help synth``):

	read -sv tests/simple/fiedler-cooley.v
	synth -top up3down5

	# mapping to target cells
	dfflibmap -liberty mycells.lib
	abc -liberty mycells.lib
	clean

The command ``prep`` provides a good default word-level synthesis script, as
used in SMT-based formal verification.


Unsupported Verilog-2005 Features
=================================

The following Verilog-2005 features are not supported by
Yosys and there are currently no plans to add support
for them:

- Non-synthesizable language features as defined in
	IEC 62142(E):2005 / IEEE Std. 1364.1(E):2002

- The ``tri``, ``triand`` and ``trior`` net types

- The ``config`` and ``disable`` keywords and library map files


Verilog Attributes and non-standard features
============================================

- The ``full_case`` attribute on case statements is supported
  (also the non-standard ``// synopsys full_case`` directive)

- The ``parallel_case`` attribute on case statements is supported
  (also the non-standard ``// synopsys parallel_case`` directive)

- The ``// synopsys translate_off`` and ``// synopsys translate_on``
  directives are also supported (but the use of ``` `ifdef .. `endif ```
  is strongly recommended instead).

- The ``nomem2reg`` attribute on modules or arrays prohibits the
  automatic early conversion of arrays to separate registers. This
  is potentially dangerous. Usually the front-end has good reasons
  for converting an array to a list of registers. Prohibiting this
  step will likely result in incorrect synthesis results.

- The ``mem2reg`` attribute on modules or arrays forces the early
  conversion of arrays to separate registers.

- The ``nomeminit`` attribute on modules or arrays prohibits the
  creation of initialized memories. This effectively puts ``mem2reg``
  on all memories that are written to in an ``initial`` block and
  are not ROMs.

- The ``nolatches`` attribute on modules or always-blocks
  prohibits the generation of logic-loops for latches. Instead
  all not explicitly assigned values default to x-bits. This does
  not affect clocked storage elements such as flip-flops.

- The ``nosync`` attribute on registers prohibits the generation of a
  storage element. The register itself will always have all bits set
  to 'x' (undefined). The variable may only be used as blocking assigned
  temporary variable within an always block. This is mostly used internally
  by Yosys to synthesize Verilog functions and access arrays.

- The ``onehot`` attribute on wires mark them as one-hot state register. This
  is used for example for memory port sharing and set by the fsm_map pass.

- The ``blackbox`` attribute on modules is used to mark empty stub modules
  that have the same ports as the real thing but do not contain information
  on the internal configuration. This modules are only used by the synthesis
  passes to identify input and output ports of cells. The Verilog backend
  also does not output blackbox modules on default. ``read_verilog``, unless
  called with ``-noblackbox`` will automatically set the blackbox attribute
  on any empty module it reads.

- The ``noblackbox`` attribute set on an empty module prevents ``read_verilog``
  from automatically setting the blackbox attribute on the module.

- The ``whitebox`` attribute on modules triggers the same behavior as
  ``blackbox``, but is for whitebox modules, i.e. library modules that
  contain a behavioral model of the cell type.

- The ``lib_whitebox`` attribute overwrites ``whitebox`` when ``read_verilog``
  is run in `-lib` mode. Otherwise it's automatically removed.

- The ``dynports`` attribute is used by the Verilog front-end to mark modules
  that have ports with a width that depends on a parameter.

- The ``hdlname`` attribute is used by some passes to document the original
  (HDL) name of a module when renaming a module.

- The ``keep`` attribute on cells and wires is used to mark objects that should
  never be removed by the optimizer. This is used for example for cells that
  have hidden connections that are not part of the netlist, such as IO pads.
  Setting the ``keep`` attribute on a module has the same effect as setting it
  on all instances of the module.

- The ``keep_hierarchy`` attribute on cells and modules keeps the ``flatten``
  command from flattening the indicated cells and modules.

- The ``init`` attribute on wires is set by the frontend when a register is
  initialized "FPGA-style" with ``reg foo = val``. It can be used during
  synthesis to add the necessary reset logic.

- The ``top`` attribute on a module marks this module as the top of the
  design hierarchy. The ``hierarchy`` command sets this attribute when called
  with ``-top``. Other commands, such as ``flatten`` and various backends
  use this attribute to determine the top module.

- The ``src`` attribute is set on cells and wires created by to the string
  ``<hdl-file-name>:<line-number>`` by the HDL front-end and is then carried
  through the synthesis. When entities are combined, a new |-separated
  string is created that contains all the string from the original entities.

- The ``defaultvalue`` attribute is used to store default values for
  module inputs. The attribute is attached to the input wire by the HDL
  front-end when the input is declared with a default value.

- The ``parameter`` and ``localparam`` attributes are used to mark wires
  that represent module parameters or localparams (when the HDL front-end
  is run in ``-pwires`` mode).

- Wires marked with the ``hierconn`` attribute are connected to wires with the
  same name (format ``cell_name.identifier``) when they are imported from
  sub-modules by ``flatten``.

- The ``clkbuf_driver`` attribute can be set on an output port of a blackbox
  module to mark it as a clock buffer output, and thus prevent ``clkbufmap``
  from inserting another clock buffer on a net driven by such output.

- The ``clkbuf_sink`` attribute can be set on an input port of a module to
  request clock buffer insertion by the ``clkbufmap`` pass.

- The ``clkbuf_inhibit`` is the default attribute to set on a wire to prevent
  automatic clock buffer insertion by ``clkbufmap``. This behaviour can be
  overridden by providing a custom selection to ``clkbufmap``.

- The ``invertible_pin`` attribute can be set on a port to mark it as
  invertible via a cell parameter.  The name of the inversion parameter
  is specified as the value of this attribute.  The value of the inversion
  parameter must be of the same width as the port, with 1 indicating
  an inverted bit and 0 indicating a non-inverted bit.

- The ``iopad_external_pin`` attribute on a blackbox module's port marks
  it as the external-facing pin of an I/O pad, and prevents ``iopadmap``
  from inserting another pad cell on it.

- The module attribute ``abc_box_id`` specifies a positive integer linking a
  blackbox or whitebox definition to a corresponding entry in a `abc9`
  box-file.

- The port attribute ``abc_carry`` marks the carry-in (if an input port) and
  carry-out (if output port) ports of a box. This information is necessary for
  `abc9` to preserve the integrity of carry-chains. Specifying this attribute
  onto a bus port will affect only its most significant bit.

- The port attribute ``abc_arrival`` specifies an integer (for output ports
  only) to be used as the arrival time of this sequential port. It can be used,
  for example, to specify the clk-to-Q delay of a flip-flop for consideration
  during techmapping.

- In addition to the ``(* ... *)`` attribute syntax, Yosys supports
  the non-standard ``{* ... *}`` attribute syntax to set default attributes
  for everything that comes after the ``{* ... *}`` statement. (Reset
  by adding an empty ``{* *}`` statement.)

- In module parameter and port declarations, and cell port and parameter
  lists, a trailing comma is ignored. This simplifies writing Verilog code
  generators a bit in some cases.

- Modules can be declared with ``module mod_name(...);`` (with three dots
  instead of a list of module ports). With this syntax it is sufficient
  to simply declare a module port as 'input' or 'output' in the module
  body.

- When defining a macro with `define, all text between triple double quotes
  is interpreted as macro body, even if it contains unescaped newlines. The
  triple double quotes are removed from the macro body. For example:

      `define MY_MACRO(a, b) """
         assign a = 23;
         assign b = 42;
      """

- The attribute ``via_celltype`` can be used to implement a Verilog task or
  function by instantiating the specified cell type. The value is the name
  of the cell type to use. For functions the name of the output port can
  be specified by appending it to the cell type separated by a whitespace.
  The body of the task or function is unused in this case and can be used
  to specify a behavioral model of the cell type for simulation. For example:

      module my_add3(A, B, C, Y);
        parameter WIDTH = 8;
        input [WIDTH-1:0] A, B, C;
        output [WIDTH-1:0] Y;
        ...
      endmodule

      module top;
        ...
        (* via_celltype = "my_add3 Y" *)
        (* via_celltype_defparam_WIDTH = 32 *)
        function [31:0] add3;
          input [31:0] A, B, C;
          begin
            add3 = A + B + C;
          end
        endfunction
        ...
      endmodule

- A limited subset of DPI-C functions is supported. The plugin mechanism
  (see ``help plugin``) can be used to load .so files with implementations
  of DPI-C routines. As a non-standard extension it is possible to specify
  a plugin alias using the ``<alias>:`` syntax. For example:

      module dpitest;
        import "DPI-C" function foo:round = real my_round (real);
        parameter real r = my_round(12.345);
      endmodule

      $ yosys -p 'plugin -a foo -i /lib/libm.so; read_verilog dpitest.v'

- Sized constants (the syntax ``<size>'s?[bodh]<value>``) support constant
  expressions as ``<size>``. If the expression is not a simple identifier, it
  must be put in parentheses. Examples: ``WIDTH'd42``, ``(4+2)'b101010``

- The system tasks ``$finish``, ``$stop`` and ``$display`` are supported in
  initial blocks in an unconditional context (only if/case statements on
  expressions over parameters and constant values are allowed). The intended
  use for this is synthesis-time DRC.

- There is limited support for converting specify .. endspecify statements to
  special ``$specify2``, ``$specify3``, and ``$specrule`` cells, for use in
  blackboxes and whiteboxes. Use ``read_verilog -specify`` to enable this
  functionality. (By default specify .. endspecify blocks are ignored.)


Non-standard or SystemVerilog features for formal verification
==============================================================

- Support for ``assert``, ``assume``, ``restrict``, and ``cover`` is enabled
  when ``read_verilog`` is called with ``-formal``.

- The system task ``$initstate`` evaluates to 1 in the initial state and
  to 0 otherwise.

- The system function ``$anyconst`` evaluates to any constant value. This is
  equivalent to declaring a reg as ``rand const``, but also works outside
  of checkers. (Yosys also supports ``rand const`` outside checkers.)

- The system function ``$anyseq`` evaluates to any value, possibly a different
  value in each cycle. This is equivalent to declaring a reg as ``rand``,
  but also works outside of checkers. (Yosys also supports ``rand``
  variables outside checkers.)

- The system functions ``$allconst`` and ``$allseq`` can be used to construct
  formal exist-forall problems. Assumptions only hold if the trace satisfies
  the assumption for all ``$allconst/$allseq`` values. For assertions and cover
  statements it is sufficient if just one ``$allconst/$allseq`` value triggers
  the property (similar to ``$anyconst/$anyseq``).

- Wires/registers declared using the ``anyconst/anyseq/allconst/allseq`` attribute
  (for example ``(* anyconst *) reg [7:0] foobar;``) will behave as if driven
  by a ``$anyconst/$anyseq/$allconst/$allseq`` function.

- The SystemVerilog tasks ``$past``, ``$stable``, ``$rose`` and ``$fell`` are
  supported in any clocked block.

- The syntax ``@($global_clock)`` can be used to create FFs that have no
  explicit clock input (``$ff`` cells). The same can be achieved by using
  ``@(posedge <netname>)`` or ``@(negedge <netname>)`` when ``<netname>``
  is marked with the ``(* gclk *)`` Verilog attribute.


Supported features from SystemVerilog
=====================================

When ``read_verilog`` is called with ``-sv``, it accepts some language features
from SystemVerilog:

- The ``assert`` statement from SystemVerilog is supported in its most basic
  form. In module context: ``assert property (<expression>);`` and within an
  always block: ``assert(<expression>);``. It is transformed to an ``$assert`` cell.

- The ``assume``, ``restrict``, and ``cover`` statements from SystemVerilog are
  also supported. The same limitations as with the ``assert`` statement apply.

- The keywords ``always_comb``, ``always_ff`` and ``always_latch``, ``logic``
  and ``bit`` are supported.

- Declaring free variables with ``rand`` and ``rand const`` is supported.

- Checkers without a port list that do not need to be instantiated (but instead
  behave like a named block) are supported.

- SystemVerilog packages are supported. Once a SystemVerilog file is read
  into a design with ``read_verilog``, all its packages are available to
  SystemVerilog files being read into the same design afterwards.

- SystemVerilog interfaces (SVIs) are supported. Modports for specifying whether
  ports are inputs or outputs are supported.


Building the documentation
==========================

Note that there is no need to build the manual if you just want to read it.
Simply download the PDF from http://www.clifford.at/yosys/documentation.html
instead.

On Ubuntu, texlive needs these packages to be able to build the manual:

	sudo apt-get install texlive-binaries
	sudo apt-get install texlive-science      # install algorithm2e.sty
	sudo apt-get install texlive-bibtex-extra # gets multibib.sty
	sudo apt-get install texlive-fonts-extra  # gets skull.sty and dsfont.sty
	sudo apt-get install texlive-publishers   # IEEEtran.cls

Also the non-free font luximono should be installed, there is unfortunately
no Ubuntu package for this so it should be installed separately using
`getnonfreefonts`:

	wget https://tug.org/fonts/getnonfreefonts/install-getnonfreefonts
	sudo texlua install-getnonfreefonts # will install to /usr/local by default, can be changed by editing BINDIR at MANDIR at the top of the script
	getnonfreefonts luximono # installs to /home/user/texmf

Then execute, from the root of the repository:

	make manual

Notes:

- To run `make manual` you need to have installed Yosys with `make install`,
  otherwise it will fail on finding `kernel/yosys.h` while building
  `PRESENTATION_Prog`.
