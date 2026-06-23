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
   an alternative which does not rely on :program:`git`.

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

A C++ compiler with C++20 support is required as well as some standard tools
such as GNU Flex, GNU Bison (>=3.8), CMake (>=3.28), Make (or other CMake
generator such as Ninja), and Python (>=3.11). Some additional tools: readline,
libffi, Tcl and zlib; will be used if available but are optional. Graphviz and
Xdot are used by the `show` command to display schematics.

Installing all prerequisites:

.. tab:: Ubuntu 22.04

   .. code:: console

      sudo apt-get install gawk git make python3 lld bison clang flex \
         libffi-dev libfl-dev libreadline-dev pkg-config tcl-dev zlib1g-dev \
         graphviz xdot
      sudo snap install cmake --classic

.. tab:: Ubuntu 24.04

   .. code:: console

      sudo apt-get install gawk git cmake make python3 lld bison clang flex \
         libffi-dev libfl-dev libreadline-dev pkg-config tcl-dev zlib1g-dev \
         graphviz xdot

.. tab:: macOS 13 (with Homebrew)

   .. code:: console

      brew tap Homebrew/bundle && brew bundle

.. tab:: MacPorts

   .. code:: console

      sudo port install bison cmake flex readline gawk libffi graphviz \
         pkgconfig python311 zlib tcl

.. tab:: FreeBSD

   .. code:: console

      pkg install bison cmake-core flex readline gawk libffi graphviz \
         pkgconf python311 tcl-wrapper

.. tab:: Cygwin

   Use the following command to install all prerequisites, or select these
   additional packages:

   .. code:: console

      setup-x86_64.exe -q --packages=bison,flex,gcc-core,gcc-g++,git,libffi-devel,libreadline-devel,cmake,make,pkg-config,python3,tcl-devel,zlib-devel

   .. warning::

      As of this writing, Cygwin only supports up to Python 3.9.16 while the
      minimum required version of Python is 3.11.  This means that Cygwin is not
      compatible with many of the Python-based frontends.  While this does not
      currently prevent Yosys itself from working, no guarantees are made for
      continued support.  You may also need to specify ``CXXSTD=gnu++20`` to
      resolve missing ``strdup`` function when using gcc.  It is instead
      recommended to use Windows Subsystem for Linux (WSL) and follow the
      instructions for Ubuntu.

..
   tab:: MSYS2 (MINGW64)

   .. code:: console

      pacman -S bison flex mingw-w64-x86_64-gcc git libffi-devel libreadline-devel make pkg-config python3 tcl-devel zlib-devel

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

The Yosys build is configured via CMake, and uses a number of variables which
influence the build process.  When setting one-off variables, CMake provides the
``-D <var>=<value>`` command line option. For example, disabling zlib support:

.. code:: console

   cmake -B build . -DYOSYS_WITHOUT_ZLIB=ON

.. warning::

   Yosys does not support in-tree builds. If calling :program:`cmake` from the
   root ``yosys`` directory the ``-B`` option must be provided.

For a more persistent configuration, we recommend creating and using a
``CMakeUserPresets.json`` file in the root ``yosys`` directory. Below is an
example file which enables ccache and sets the default compiler to clang when
calling ``cmake --preset default``:

.. code-block:: json
   :caption: CMakeUserPresets.json

   {
      "version": 1,
      "configurePresets": [
         {
            "name": "default",
            "binaryDir": "build",
            "generator": "Unix Makefiles",
            "cacheVariables": {
               "CMAKE_C_COMPILER": "clang",
               "CMAKE_CXX_COMPILER": "clang++",
               "YOSYS_COMPILER_LAUNCHER": "ccache"
            }
         }
      ]
   }

Once generated, available build variables can be inspected and modified with
:program:`ccmake` or opening the generated ``build/CMakeCache.txt`` file:

.. code:: console

   ccmake build              #..or..
   vi build/CMakeCache.txt

If you have clang, and (a compatible version of) ``ld.lld`` available in PATH,
it's recommended to speed up incremental builds with lld by enabling LTO with
``CMAKE_INTERPROCEDURAL_OPTIMIZATION=ON``.  On macOS, LTO requires using clang
from homebrew rather than clang from xcode.  For example:

.. code:: console

   cmake -B build . -DCMAKE_INTERPROCEDURAL_OPTIMIZATION=ON \
      -DCMAKE_C_COMPILER=$(brew --prefix)/opt/llvm/bin/clang \
      -DCMAKE_CXX_COMPILER=$(brew --prefix)/opt/llvm/bin/clang++

By default, building (and installing) Yosys will build (and install) `ABC`_,
using :program:`yosys-abc` as the executable name.  To use an existing ABC
executable instead, set the :makevar:`YOSYS_ABC_EXECUTABLE` CMake variable to
point to the desired executable.

Running the build system
^^^^^^^^^^^^^^^^^^^^^^^^

To quickly install Yosys with default settings, call the following commands from
the root ``yosys`` directory:

.. code:: console

   cmake -B build . -DCMAKE_BUILD_TYPE=Release --fresh
   cmake --build build --config Release --parallel $(nproc)
   sudo cmake --install build --strip

To use an existing configuration, use the ``--build`` option, e.g:

.. code:: console

   cmake -B build .
   ccmake build              # modify configuration
   cmake --build build

.. seealso::

   Refer to :doc:`/yosys_internals/extending_yosys/test_suites` for details on
   testing Yosys once compiled.

Source tree and build system
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The Yosys source tree is organized into the following top-level
directories:

``backends/``
   This directory contains a subdirectory for each of the backend modules.

``cmake/``
   Additional ``.cmake`` files used by CMake during build generation.

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

``pyosys/``
   Contains the scripts and wrappers necessary for building :doc:`Pyosys
   </using_yosys/pyosys>`.

``techlibs/``
   This directory contains simulation models and standard implementations for
   the cells from the internal cell library.

``tests/``
   This directory contains the suite of unit tests and regression tests used by
   Yosys.  See :doc:`/yosys_internals/extending_yosys/test_suites`.

.. TODO:: CMAKE_TODO

   - ``yosys_<pass|test_pass|frontend|backend>(<name>)`` for each pass

      - see :file:`cmake/YosysComponent.cmake`

   - if using a sub folder, add it to the parent's ``CMakeLists.txt`` with
     ``add_subdirectory(<name>)``

   - previous:

   The Yosys kernel automatically detects all commands linked
   with Yosys. So it is not needed to add additional commands to a central list of
   commands.

   Good starting points for reading example source code to learn how to write
   passes are :file:`passes/opt/opt_dff.cc` and :file:`passes/opt/opt_merge.cc`.

   Users of the Qt Creator IDE can generate a QT Creator project file using make
   qtcreator. Users of the Eclipse IDE can use the "Makefile Project with Existing
   Code" project type in the Eclipse "New Project" dialog (only available after the
   CDT plugin has been installed) to create an Eclipse project in order to
   programming extensions to Yosys or just browse the Yosys code base.
