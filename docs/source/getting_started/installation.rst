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

.. only:: html

   - linux-x64 |linux-x64|
      - Most personal Linux based computers

   - darwin-x64 |darwin-x64|
      - macOS 12 or later with Intel CPU

   - darwin-arm64 |darwin-arm64|
      - macOS 12 or later with M1/M2 CPU

   - windows-x64 |windows-x64|
      - Targeted for Windows 10 and 11

   - linux-arm64 |linux-arm64|

.. _OSS CAD Suite: https://github.com/YosysHQ/oss-cad-suite-build
.. _nightly builds: https://github.com/YosysHQ/oss-cad-suite-build/releases/latest

.. |linux-x64| image:: https://github.com/YosysHQ/oss-cad-suite-build/actions/workflows/linux-x64.yml/badge.svg
.. |darwin-x64| image:: https://github.com/YosysHQ/oss-cad-suite-build/actions/workflows/darwin-x64.yml/badge.svg
.. |darwin-arm64| image:: https://github.com/YosysHQ/oss-cad-suite-build/actions/workflows/darwin-arm64.yml/badge.svg
.. |windows-x64| image:: https://github.com/YosysHQ/oss-cad-suite-build/actions/workflows/windows-x64.yml/badge.svg
.. |linux-arm64| image:: https://github.com/YosysHQ/oss-cad-suite-build/actions/workflows/linux-arm64.yml/badge.svg

Building from source
~~~~~~~~~~~~~~~~~~~~

Refer to the `readme`_ for the most up-to-date install instructions.

.. _readme: https://github.com/YosysHQ/yosys#building-from-source

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
:cmd:ref:`show` command to display schematics.

Installing all prerequisites for Ubuntu 20.04:

.. code:: console

   sudo sudo apt-get install build-essential clang bison flex \
      libreadline-dev gawk tcl-dev libffi-dev git make \
      graphviz xdot pkg-config python3 libboost-system-dev \
      libboost-python-dev libboost-filesystem-dev zlib1g-dev

Installing all prerequisites for macOS 11 (with Homebrew):

.. code:: console

   brew install bison flex gawk libffi git graphviz \
      pkg-config python3 tcl-tk xdot bash boost-python3

Running the build system
^^^^^^^^^^^^^^^^^^^^^^^^

From the root `yosys` directory, call the following commands:

.. code:: console
   
   make
   sudo make install

This will build and then install Yosys, making it available on the command line
as `yosys`.  Note that this also downloads, builds, and installs `ABC`_ (using
:program:`yosys-abc` as the executable name).

.. _ABC: https://github.com/berkeley-abc/abc

The default compiler is ``clang``, to change between ``clang`` and ``gcc``, use
one of the following:

.. code:: console

   make config-clang
   make config-gcc

To use a compiler different than the default, use:

.. code:: console

   make CXX="g++-11"

.. seealso:: 

   Refer to :doc:`/test_suites` for details on testing Yosys once compiled.

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

``guidelines/``
   Contains developer guidelines, including the code of conduct and coding style
   guide.

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
   example as of this writing the directory :file:`passes/hierarchy/` contains the
   code for three passes: :cmd:ref:`hierarchy`, :cmd:ref:`submod`, and
   :cmd:ref:`uniquify`.

``techlibs/``
   This directory contains simulation models and standard implementations for
   the cells from the internal cell library.

``tests/``
   This directory contains the suite of unit tests and regression tests used by
   Yosys.  See :doc:`/test_suites`.

The top-level Makefile includes :file:`frontends/{*}/Makefile.inc`,
:file:`passes/{*}/Makefile.inc` and :file:`backends/{*}/Makefile.inc`. So when
extending Yosys it is enough to create a new directory in :file:`frontends/`,
:file:`passes/` or :file:`backends/` with your sources and a
:file:`Makefile.inc`. The Yosys kernel automatically detects all commands linked
with Yosys. So it is not needed to add additional commands to a central list of
commands.

Good starting points for reading example source code to learn how to write
passes are :file:`passes/opt/opt_dff.cc` and :file:`passes/opt/opt_merge.cc`.

See the top-level README file for a quick Getting Started guide and build
instructions. The Yosys build is based solely on Makefiles.

Users of the Qt Creator IDE can generate a QT Creator project file using make
qtcreator. Users of the Eclipse IDE can use the "Makefile Project with Existing
Code" project type in the Eclipse "New Project" dialog (only available after the
CDT plugin has been installed) to create an Eclipse project in order to
programming extensions to Yosys or just browse the Yosys code base.
