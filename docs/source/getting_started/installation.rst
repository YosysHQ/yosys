Installation
------------

This document will guide you through the process of installing Yosys.

CAD suite(s)
~~~~~~~~~~~~

Yosys is part of the `Tabby CAD Suite
<https://www.yosyshq.com/tabby-cad-datasheet>`_ and the `OSS CAD Suite
<https://github.com/YosysHQ/oss-cad-suite-build>`_! The easiest way to use yosys
is to install the binary software suite, which contains all required
dependencies and related tools.

* `Contact YosysHQ <https://www.yosyshq.com/contact>`_ for a `Tabby CAD Suite
  <https://www.yosyshq.com/tabby-cad-datasheet>`_ Evaluation License and
  download link
* OR go to https://github.com/YosysHQ/oss-cad-suite-build/releases to download
  the free OSS CAD Suite
* Follow the `Install Instructions on GitHub
  <https://github.com/YosysHQ/oss-cad-suite-build#installation>`_

Make sure to get a Tabby CAD Suite Evaluation License if you need features such
as industry-grade SystemVerilog and VHDL parsers!

For more information about the difference between Tabby CAD Suite and the OSS
CAD Suite, please visit https://www.yosyshq.com/tabby-cad-datasheet

Many Linux distributions also provide Yosys binaries, some more up to date than
others. Check with your package manager!

Targeted architectures
^^^^^^^^^^^^^^^^^^^^^^

The `OSS CAD Suite`_ releases `nightly builds`_ for the following architectures:

- **linux-x64** - Most personal Linux based computers
- **darwin-x64** - macOS 12 or later with Intel CPU
- **darwin-arm64** - macOS 12 or later with M1/M2 CPU
- **windows-x64** - Targeted for Windows 10 and 11
- **linux-arm64** - Devices such as Raspberry Pi with 64bit OS

For more information about the targeted architectures, and the current build
status, check the `OSS CAD Suite`_ git repository.

.. _OSS CAD Suite: https://github.com/YosysHQ/oss-cad-suite-build
.. _nightly builds: https://github.com/YosysHQ/oss-cad-suite-build/releases/latest

Building from source
~~~~~~~~~~~~~~~~~~~~

The Yosys source files can be obtained from the `YosysHQ/Yosys git repository`_.
`ABC`_ and some of the other libraries used are included as git submodules.  To
clone these submodules at the same time, use e.g.:

.. code:: console

   git clone --recurse-submodules https://github.com/YosysHQ/yosys.git  # ..or..
   git clone https://github.com/YosysHQ/yosys.git
   cd yosys
   git submodule update --init --recursive

.. _YosysHQ/Yosys git repository: https://github.com/yosyshq/yosys/
.. _ABC: https://github.com/berkeley-abc/abc

.. note::

   As of Yosys v0.47, releases include a ``yosys.tar.gz`` file which includes
   all source code and all sub-modules in a single archive.  This can be used as
   an alternative which does not rely on ``git``.

Supported platforms
^^^^^^^^^^^^^^^^^^^

The following platforms are supported and regularly tested:

- Linux
- macOS

Other platforms which may work, but instructions may not be up to date and are
not regularly tested:

- FreeBSD
- WSL
- Windows with (e.g.) Cygwin

Build prerequisites
^^^^^^^^^^^^^^^^^^^

A C++ compiler with C++17 support is required as well as some standard tools
such as GNU Flex, GNU Bison, Make and Python.  Some additional tools: readline,
libffi, Tcl and zlib; are optional but enabled by default (see
:makevar:`ENABLE_*` settings in Makefile). Graphviz and Xdot are used by the
`show` command to display schematics.

Installing all prerequisites for Ubuntu 20.04:

.. code:: console

   sudo apt-get install gperf build-essential bison flex \
      libreadline-dev gawk tcl-dev libffi-dev git graphviz \
      xdot pkg-config python3 libboost-system-dev \
      libboost-python-dev libboost-filesystem-dev zlib1g-dev

Installing all prerequisites for macOS 13 (with Homebrew):

.. code:: console

   brew tap Homebrew/bundle && brew bundle

or MacPorts:

.. code:: console

   sudo port install bison flex readline gawk libffi graphviz \
      pkgconfig python311 boost zlib tcl

On FreeBSD use the following command to install all prerequisites:

.. code:: console

   pkg install bison flex readline gawk libffi graphviz \
      pkgconf python311 tcl-wrapper boost-libs

.. note:: On FreeBSD system use gmake instead of make. To run tests use:
    ``MAKE=gmake CXX=cxx CC=cc gmake test``

For Cygwin use the following command to install all prerequisites, or select these additional packages:

.. code:: console

   setup-x86_64.exe -q --packages=bison,flex,gcc-core,gcc-g++,git,libffi-devel,libreadline-devel,make,pkg-config,python3,tcl-devel,boost-build,zlib-devel

.. warning::

   As of this writing, Cygwin only supports up to Python 3.9.16 while the
   minimum required version of Python is 3.11.  This means that Cygwin is not
   compatible with many of the Python-based frontends.  While this does not
   currently prevent Yosys itself from working, no guarantees are made for
   continued support.  It is instead recommended to use Windows Subsystem for
   Linux (WSL) and follow the instructions for Ubuntu.

.. 
   For MSYS2 (MINGW64):

   .. code:: console

      pacman -S bison flex mingw-w64-x86_64-gcc git libffi-devel libreadline-devel make pkg-config python3 tcl-devel mingw-w64-x86_64-boost zlib-devel

   Not that I can get this to work; it's failing during ld with what looks like
   math library issues: ``multiple definition of `tanh'`` and
   ``undefined reference to `__imp_acosh'``, as well as issues in `aiger2` with
   ``seekg`` et al not being available.

   .. note::

      The ``config-msys2-64`` target uses the ``mingw-w64-x86_64-`` prefixed
      compiler in order to allow compiled exe files to be run without an MSYS2
      shell.

Build configuration
^^^^^^^^^^^^^^^^^^^

The Yosys build is based solely on Makefiles, and uses a number of variables
which influence the build process.  The recommended method for configuring
builds is with a ``Makefile.conf`` file in the root ``yosys`` directory. The
following commands will clean the directory and provide an initial configuration
file:

.. code:: console

   make config-clang    # ..or..
   make config-gcc

Check the root Makefile to see what other configuration targets are available.
Other variables can then be added to the ``Makefile.conf`` as needed, for
example:

.. code:: console

   echo "ENABLE_ZLIB := 0" >> Makefile.conf

Using one of these targets will set the ``CONFIG`` variable to something other
than ``none``, and will override the environment variable for ``CXX``.  To use a
different compiler than the default when building, use:

.. code:: console

   make CXX=$CXX        # ..or..
   make CXX="g++-11"

.. note::

   Setting the compiler in this way will prevent some other options such as
   ``ENABLE_CCACHE`` from working as expected.

If you have clang, and (a compatible version of) ``ld.lld`` available in PATH,
it's recommended to speed up incremental builds with lld by enabling LTO with
``ENABLE_LTO=1``.  On macOS, LTO requires using clang from homebrew rather than
clang from xcode.  For example:

.. code:: console

   make ENABLE_LTO=1 CXX=$(brew --prefix)/opt/llvm/bin/clang++

By default, building (and installing) yosys will build (and install) `ABC`_,
using :program:`yosys-abc` as the executable name.  To use an existing ABC
executable instead, set the ``ABCEXTERNAL`` make variable to point to the
desired executable.

Running the build system
^^^^^^^^^^^^^^^^^^^^^^^^

From the root ``yosys`` directory, call the following commands:

.. code:: console
   
   make
   sudo make install

To use a separate (out-of-tree) build directory, provide a path to the Makefile.

.. code:: console

   mkdir build; cd build
   make -f ../Makefile

Out-of-tree builds require a clean source tree.

.. seealso:: 

   Refer to :doc:`/yosys_internals/extending_yosys/test_suites` for details on
   testing Yosys once compiled.

Source tree and build system
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The Yosys source tree is organized into the following top-level
directories:

``backends/``
   This directory contains a subdirectory for each of the backend modules.

``docs/``
   Contains the source for this documentation, including images and sample code.

``examples/``
   Contains example code for using Yosys with some other tools including a demo
   of the Yosys Python api, and synthesizing for various toolchains such as
   Intel and Anlogic.

``frontends/``
   This directory contains a subdirectory for each of the frontend modules.

``kernel/``
   This directory contains all the core functionality of Yosys. This includes
   the functions and definitions for working with the RTLIL data structures
   (:file:`rtlil.{h|cc}`), the ``main()`` function (:file:`driver.cc`), the
   internal framework for generating log messages (:file:`log.{h|cc}`), the
   internal framework for registering and calling passes
   (:file:`register.{h|cc}`), some core commands that are not really passes
   (:file:`select.cc`, :file:`show.cc`, …) and a couple of other small utility
   libraries.

``libs/``
   Libraries packaged with Yosys builds are contained in this folder.  See
   :doc:`/appendix/auxlibs`.

``misc/``
   Other miscellany which doesn't fit anywhere else.

``passes/``
   This directory contains a subdirectory for each pass or group of passes. For
   example as of this writing the directory :file:`passes/hierarchy/` contains
   the code for three passes: `hierarchy`, `submod`, and `uniquify`.

``techlibs/``
   This directory contains simulation models and standard implementations for
   the cells from the internal cell library.

``tests/``
   This directory contains the suite of unit tests and regression tests used by
   Yosys.  See :doc:`/yosys_internals/extending_yosys/test_suites`.

The top-level Makefile includes :file:`frontends/{*}/Makefile.inc`,
:file:`passes/{*}/Makefile.inc` and :file:`backends/{*}/Makefile.inc`. So when
extending Yosys it is enough to create a new directory in :file:`frontends/`,
:file:`passes/` or :file:`backends/` with your sources and a
:file:`Makefile.inc`. The Yosys kernel automatically detects all commands linked
with Yosys. So it is not needed to add additional commands to a central list of
commands.

Good starting points for reading example source code to learn how to write
passes are :file:`passes/opt/opt_dff.cc` and :file:`passes/opt/opt_merge.cc`.

Users of the Qt Creator IDE can generate a QT Creator project file using make
qtcreator. Users of the Eclipse IDE can use the "Makefile Project with Existing
Code" project type in the Eclipse "New Project" dialog (only available after the
CDT plugin has been installed) to create an Eclipse project in order to
programming extensions to Yosys or just browse the Yosys code base.
