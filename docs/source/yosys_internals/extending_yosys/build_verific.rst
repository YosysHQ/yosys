Compiling with Verific library
==============================

The easiest way to get Yosys with Verific support is to `contact YosysHQ`_ for a
`Tabby CAD Suite`_ evaluation license and download link.  The TabbyCAD Suite
includes additional patches and a custom extensions library in order to get the
most out of the Verific parser when using Yosys.

If you already have a license for the Verific parser, in either source or binary
form, you may be able to compile Yosys with partial Verific support yourself.

.. _contact YosysHQ : https://www.yosyshq.com/contact
.. _Tabby CAD Suite: https://www.yosyshq.com/tabby-cad-datasheet

The Yosys-Verific patch
-----------------------

YosysHQ maintains and develops a patch for Verific in order to better integrate
with Yosys and to provide features required by some of the formal verification
front-end tools.  To license this patch for your own Yosys builds, `contact
YosysHQ`_.

.. warning::

   While synthesis from RTL may be possible without this patch, YosysHQ provides
   no guarantees of correctness and is unable to provide support.

We recommend against using unpatched Yosys+Verific builds in conjunction with
the formal verification front-end tools unless you are familiar with their inner
workings. There are cases where the tools will appear to work, while producing
incorrect results.

.. note::

   Some of the formal verification front-end tools may not be fully supported
   without the full TabbyCAD suite.  If you want to use these tools, including
   SBY, make sure to ask us if the Yosys-Verific patch is right for you.

Compile options
---------------

To enable Verific support, set the :makevar:`YOSYS_VERIFIC_DIR` CMake variable
to point to the location where the library is located, e.g.

.. code-block:: console

   cmake -B build . -DYOSYS_VERIFIC_DIR="/usr/local/src/verific_lib"

During building, CMake will attempt to automatically detect available Verific
library components to enable the corresponding compile-time option in Yosys.
This can be overridden by manually setting the :makevar:`YOSYS_VERIFIC_FEATURES`
CMake variable. This variable should contain a semi-colon separated list, e.g.
``-DYOSYS_VERIFIC_FEATURES="systemverilog;hier_tree"``.  The table below lists
the features available to Yosys.

============== =========== ===================================
Feature        Directory   Description
============== =========== ===================================
systemverilog  verilog     SystemVerilog support
vhdl           vhdl        VHDL support
hier_tree      hier_tree   Hierarchy tree support
extensions     extensions  YosysHQ specific extensions support
edif           edif        EDIF support
liberty        synlib      Liberty file support
============== =========== ===================================

.. note::

   The YosysHQ specific extensions are only available with the TabbyCAD suite.

Required Verific features
~~~~~~~~~~~~~~~~~~~~~~~~~

The following features, along with their corresponding Yosys build parameters,
are required for the Yosys-Verific patch:

* RTL elaboration with

  * SystemVerilog with ``systemverilog``, and/or
  * VHDL support with ``vhdl``.

* Hierarchy tree support and static elaboration with ``hier_tree``.

Please be aware that the following Verific configuration build parameter needs
to be enabled in order to create the fully supported build:

::

   database/DBCompileFlags.h:
       DB_PRESERVE_INITIAL_VALUE

.. note::

   Yosys+Verific builds may compile without these features, but we provide no
   guarantees and cannot offer support if they are disabled or the Yosys-Verific
   patch is not used.

Optional Verific features
~~~~~~~~~~~~~~~~~~~~~~~~~

The following Verific features are available with TabbyCAD and will be
automatically enabled in Yosys builds if the listed directory is included in the
:makevar:`YOSYS_VERIFIC_DIR`:

* EDIF support with ``edif`` directory, and
* Liberty file support with ``synlib`` directory.

Partially supported builds
~~~~~~~~~~~~~~~~~~~~~~~~~~

This section describes Yosys+Verific configurations which we have confirmed as
working in the past, however they are not a part of our regular tests so we
cannot guarantee they are still functional.

To be able to compile Yosys with Verific, the Verific library must have support
for at least one HDL language with RTL elaboration enabled.  The following table
lists a series of build configurations which are possible, but only provide a
limited subset of features.  Please note that support is limited without YosysHQ
specific extensions of Verific library.

======================================================================= =================================
Features                                                                :makevar:`YOSYS_VERIFIC_FEATURES`
======================================================================= =================================
SystemVerilog + RTL elaboration                                         systemverilog
VHDL + RTL elaboration                                                  vhdl
SystemVerilog + VHDL + RTL elaboration                                  systemverilog;vhdl
SystemVerilog + RTL elaboration + Static elaboration + Hier tree        systemverilog;vhdl;hier_tree
VHDL + RTL elaboration + Static elaboration + Hier tree                 vhdl;hier_tree
SystemVerilog + VHDL + RTL elaboration + Static elaboration + Hier tree systemverilog;vhdl;hier_tree
======================================================================= =================================

.. note::

   In case your Verific build has EDIF and/or Liberty support, you can enable
   those options. These are not mentioned above for simplification.
