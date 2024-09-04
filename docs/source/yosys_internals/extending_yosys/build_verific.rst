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

To enable Verific support ``ENABLE_VERIFIC`` has to be set to ``1`` and
``VERIFIC_DIR`` needs to point to the location where the library is located.

============== ========================== ===============================
Parameter      Default                    Description
============== ========================== ===============================
ENABLE_VERIFIC 0                          Enable compilation with Verific
VERIFIC_DIR    /usr/local/src/verific_lib Library and headers location
============== ========================== ===============================

Since there are multiple Verific library builds and they can have different
features, there are compile options to select them.

================================= ======= ===================================
Parameter                         Default Description
================================= ======= ===================================
ENABLE_VERIFIC_SYSTEMVERILOG      1       SystemVerilog support
ENABLE_VERIFIC_VHDL               1       VHDL support
ENABLE_VERIFIC_HIER_TREE          1       Hierarchy tree support
ENABLE_VERIFIC_YOSYSHQ_EXTENSIONS 0       YosysHQ specific extensions support
ENABLE_VERIFIC_EDIF               0       EDIF support
ENABLE_VERIFIC_LIBERTY            0       Liberty file support
================================= ======= ===================================

To find the compile options used for a given Yosys build, call ``yosys-config
--cxxflags``. This documentation was built with the following compile options:

.. literalinclude:: /generated/yosys-config
    :start-at: --cxxflags
    :end-before: --linkflags

.. note::

   The YosysHQ specific extensions are only available with the TabbyCAD suite.

Required Verific features
~~~~~~~~~~~~~~~~~~~~~~~~~

The following features, along with their corresponding Yosys build parameters,
are required for the Yosys-Verific patch:

* RTL elaboration with

  * SystemVerilog with ``ENABLE_VERIFIC_SYSTEMVERILOG``, and/or
  * VHDL support with ``ENABLE_VERIFIC_VHDL``.

* Hierarchy tree support and static elaboration with
  ``ENABLE_VERIFIC_HIER_TREE``.

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

The following Verific features are available with TabbyCAD and can be enabled in
Yosys builds:

* EDIF support with ``ENABLE_VERIFIC_EDIF``, and
* Liberty file support with ``ENABLE_VERIFIC_LIBERTY``.

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

Configuration values:
  a. ``ENABLE_VERIFIC_SYSTEMVERILOG``
  b. ``ENABLE_VERIFIC_VHDL``
  c. ``ENABLE_VERIFIC_HIER_TREE``
  d. ``ENABLE_VERIFIC_YOSYSHQ_EXTENSIONS``

+--------------------------------------------------------------------------+-----+-----+-----+-----+
|                                                                          | Configuration values  |
+--------------------------------------------------------------------------+-----+-----+-----+-----+
| Features                                                                 |   a |   b |   c |   d |
+==========================================================================+=====+=====+=====+=====+
| SystemVerilog + RTL elaboration                                          |   1 |   0 |   0 |   0 |
+--------------------------------------------------------------------------+-----+-----+-----+-----+
| VHDL + RTL elaboration                                                   |   0 |   1 |   0 |   0 |
+--------------------------------------------------------------------------+-----+-----+-----+-----+
| SystemVerilog + VHDL + RTL elaboration                                   |   1 |   1 |   0 |   0 |
+--------------------------------------------------------------------------+-----+-----+-----+-----+
| SystemVerilog + RTL elaboration + Static elaboration + Hier tree         |   1 |   0 |   1 |   0 |
+--------------------------------------------------------------------------+-----+-----+-----+-----+
| VHDL + RTL elaboration + Static elaboration + Hier tree                  |   0 |   1 |   1 |   0 |
+--------------------------------------------------------------------------+-----+-----+-----+-----+
| SystemVerilog + VHDL + RTL elaboration + Static elaboration + Hier tree  |   1 |   1 |   1 |   0 |
+--------------------------------------------------------------------------+-----+-----+-----+-----+

.. note::

   In case your Verific build has EDIF and/or Liberty support, you can enable
   those options. These are not mentioned above for simplification and since
   they are disabled by default.
