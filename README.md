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

Third-party software distributed alongside this software
is licensed under compatible licenses.
Please refer to `abc` and `libs` subdirectories for their license terms.


Web Site and Other Resources
============================

More information and documentation can be found on the Yosys web site:
- https://yosyshq.net/yosys/

Documentation from this repository is automatically built and available on Read
the Docs:
- https://yosyshq.readthedocs.io/projects/yosys

Users interested in formal verification might want to use the formal
verification front-end for Yosys, SBY:
- https://yosyshq.readthedocs.io/projects/sby/
- https://github.com/YosysHQ/sby


Installation
============

Yosys is part of the [Tabby CAD Suite](https://www.yosyshq.com/tabby-cad-datasheet) and the [OSS CAD Suite](https://github.com/YosysHQ/oss-cad-suite-build)! The easiest way to use yosys is to install the binary software suite, which contains all required dependencies and related tools.

* [Contact YosysHQ](https://www.yosyshq.com/contact) for a [Tabby CAD Suite](https://www.yosyshq.com/tabby-cad-datasheet) Evaluation License and download link
* OR go to https://github.com/YosysHQ/oss-cad-suite-build/releases to download the free OSS CAD Suite
* Follow the [Install Instructions on GitHub](https://github.com/YosysHQ/oss-cad-suite-build#installation)

Make sure to get a Tabby CAD Suite Evaluation License if you need features such as industry-grade SystemVerilog and VHDL parsers!

For more information about the difference between Tabby CAD Suite and the OSS CAD Suite, please visit https://www.yosyshq.com/tabby-cad-datasheet

Many Linux distributions also provide Yosys binaries, some more up to date than others. Check with your package manager!


Building from Source
====================

For more details, and instructions for other platforms, check [building from
source](https://yosyshq.readthedocs.io/projects/yosys/en/latest/getting_started/installation.html#building-from-source)
on Read the Docs.

When cloning Yosys, some required libraries are included as git submodules. Make
sure to call e.g.

	$ git clone --recurse-submodules https://github.com/YosysHQ/yosys.git

or

	$ git clone https://github.com/YosysHQ/yosys.git
	$ cd yosys
	$ git submodule update --init --recursive

You need a C++ compiler with C++17 support (up-to-date CLANG or GCC is
recommended) and some standard tools such as GNU Flex, GNU Bison, and GNU Make.
TCL, readline and libffi are optional (see ``ENABLE_*`` settings in Makefile).
Xdot (graphviz) is used by the ``show`` command in yosys to display schematics.

For example on Ubuntu Linux 16.04 LTS the following commands will install all
prerequisites for building yosys:

	$ sudo apt-get install build-essential clang lld bison flex \
		libreadline-dev gawk tcl-dev libffi-dev git \
		graphviz xdot pkg-config python3 libboost-system-dev \
		libboost-python-dev libboost-filesystem-dev zlib1g-dev

The environment variable `CXX` can be used to control the C++ compiler used, or
run one of the following to override it:

	$ make config-clang
	$ make config-gcc

The Makefile has many variables influencing the build process. These can be
adjusted by modifying the Makefile.conf file which is created at the `make
config-...` step (see above), or they can be set by passing an option to the
make command directly:

  $ make CXX=$CXX

For other compilers and build configurations it might be necessary to make some
changes to the config section of the Makefile. It's also an alternative way to
set the make variables mentioned above.

	$ vi Makefile            # ..or..
	$ vi Makefile.conf

To build Yosys simply type 'make' in this directory.

	$ make
	$ sudo make install

Tests are located in the tests subdirectory and can be executed using the test
target. Note that you need gawk as well as a recent version of iverilog (i.e.
build from git). Then, execute tests via:

	$ make test

To use a separate (out-of-tree) build directory, provide a path to the Makefile.

	$ mkdir build; cd build
	$ make -f ../Makefile

Out-of-tree builds require a clean source tree.


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

writing the design to the console in the RTLIL format used by Yosys
internally:

	yosys> write_rtlil

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


Additional information
======================

The ``read_verilog`` command, used by default when calling ``read`` with Verilog
source input, does not perform syntax checking.  You should instead lint your
source with another tool such as
[Verilator](https://www.veripool.org/verilator/) first, e.g. by calling
``verilator --lint-only``.


Building the documentation
==========================

Note that there is no need to build the manual if you just want to read it.
Simply visit https://yosys.readthedocs.io/en/latest/ instead.

In addition to those packages listed above for building Yosys from source, the
following are used for building the website: 

	$ sudo apt install pdf2svg faketime

Or for MacOS, using homebrew:

  $ brew install pdf2svg libfaketime

PDFLaTeX, included with most LaTeX distributions, is also needed during the
build process for the website.  Or, run the following:

	$ sudo apt install texlive-latex-base texlive-latex-extra latexmk

Or for MacOS, using homebrew:

  $ brew install basictex
  $ sudo tlmgr update --self   
  $ sudo tlmgr install collection-latexextra latexmk tex-gyre

The Python package, Sphinx, is needed along with those listed in
`docs/source/requirements.txt`:

	$ pip install -U sphinx -r docs/source/requirements.txt

From the root of the repository, run `make docs`.  This will build/rebuild yosys
as necessary before generating the website documentation from the yosys help
commands.  To build for pdf instead of html, call 
`make docs DOC_TARGET=latexpdf`.
