Installation
------------

Supported platforms
~~~~~~~~~~~~~~~~~~~

Source tree and build system
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

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
