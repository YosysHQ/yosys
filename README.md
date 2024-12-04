```
yosys -- Yosys Open SYnthesis Suite

Copyright (C) 2012 - 2024  Claire Xenia Wolf <claire@yosyshq.com>

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

Third-party software distributed alongside this software
is licensed under compatible licenses.
Please refer to `abc` and `libs` subdirectories for their license terms.

Web Site and Other Resources
============================

More information and documentation can be found on the Yosys web site:
- https://yosyshq.net/yosys/

The "Documentation" page on the web site contains links to more resources,
including a manual that even describes some of the Yosys internals:
- https://yosyshq.net/yosys/documentation.html

Users interested in formal verification might want to use the formal verification
front-end for Yosys, SymbiYosys:
- https://symbiyosys.readthedocs.io/en/latest/
- https://github.com/YosysHQ/SymbiYosys


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

Similarily, on Mac OS X Homebrew can be used to install dependencies (from within cloned yosys repository):

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

The environment variable `CXX` can be used to control the C++ compiler used, or
run one of the following:

	$ make config-clang
	$ make config-gcc

Note that these will result in `make` ignoring the `CXX` environment variable,
unless `CXX` is assigned in the call to make, e.g.

  $ make CXX=$CXX

The Makefile has many variables influencing the build process. These can be
adjusted by modifying the Makefile.conf file which is created at the
`make config-...` step (see above), or they can be set by passing an option
to the make command directly.

For example, if you have clang, and (a compatible version of) `ld.lld`
available in PATH, it's recommended to speed up incremental builds with
lld by enabling LTO:

 $ make ENABLE_LTO=1

On macOS, LTO requires using clang from homebrew which isn't in PATH
rather than xcode clang.

$ make ENABLE_LTO=1 CXX=$(brew --prefix)/opt/llvm/bin/clang++

For other compilers and build configurations it might be
necessary to make some changes to the config section of the
Makefile. It's also an alternative way to set the make variables
mentioned above.

	$ vi Makefile            # ..or..
	$ vi Makefile.conf

To build Yosys simply type 'make' in this directory.

	$ make
	$ sudo make install

Note that this also downloads, builds and installs ABC (using yosys-abc
as executable name).

Tests are located in the tests subdirectory and can be executed using the test target. Note that you need gawk as well as a recent version of iverilog (i.e. build from git). Then, execute tests via:

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

Building for Windows
====================

Creating the Visual Studio Template Project
-------------------------------------------

1. Create an empty Visual C++ Win32 Console App project

	Microsoft Visual Studio Express 2013 for Windows Desktop
	Open New Project Wizard (File -> New Project..)

	Project Name: YosysVS
	Solution Name: YosysVS
	[X] Create directory for solution
	[ ] Add to source control

	[X] Console applications
	[X] Empty Project
	[ ] SDL checks

2. Open YosysVS Project Properties

	Select Configuration: All Configurations

	C/C++ -> General -> Additional Include Directories
		Add: ..\yosys

	C/C++ -> Preprocessor -> Preprocessor Definitions
		Add: _YOSYS_;_CRT_SECURE_NO_WARNINGS

3. Resulting file system tree:

	YosysVS/
	YosysVS/YosysVS
	YosysVS/YosysVS/YosysVS.vcxproj
	YosysVS/YosysVS/YosysVS.vcxproj.filters
	YosysVS/YosysVS.sdf
	YosysVS/YosysVS.sln
	YosysVS/YosysVS.v12.suo

4. Zip YosysVS as YosysVS-Tpl-v1.zip

Compiling with Visual Studio
----------------------------

Visual Studio builds are not directly supported by build scripts, but they are still possible.

1. Easy way

  - Go to https://github.com/YosysHQ/yosys/actions/workflows/vs.yml?query=branch%3Amain
  - Click on the most recent completed run
  - In Artifacts region find vcxsrc and click on it to download
  - Unpack downloaded ZIP file
  - Open YosysVS.sln with Visual Studio
  
2. Using WSL or MSYS2

  - Make sure to have make, python3 and git available
  - Git clone yosys repository
  - Execute ```make vcxsrc YOSYS_VER=latest```
  - File yosys-win32-vcxsrc-latest.zip will be created
  - Transfer that file to location visible by Windows application
  - Unpack ZIP
  - Open YosysVS.sln with Visual Studio
