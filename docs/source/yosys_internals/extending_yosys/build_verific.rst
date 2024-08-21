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

.. todo:: Fill out section on Yosys-Verific patch

* Yosys-Verific patch developed for best integration
* Needed for some of the formal verification front-end tools
* `contact YosysHQ`_ about licensing this patch for your own Yosys builds
* Unable to provide support for builds without this patch

New cells
~~~~~~~~~

============== ===========
Cell           Description
============== ===========
$initstate    
$set_tag      
$get_tag      
$overwrite_tag
$original_tag 
$future_ff    
============== ===========

.. todo:: (sub)section on features only available with TabbyCAD

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
ENABLE_VERIFIC_YOSYSHQ_EXTENSIONS 1       YosysHQ specific extensions support
ENABLE_VERIFIC_EDIF               0       EDIF support
ENABLE_VERIFIC_LIBERTY            0       Liberty file support
================================= ======= ===================================

Supported build
~~~~~~~~~~~~~~~

The default values for options represent the only fully supported configuration
of Yosys with Verific. This build includes SystemVerilog and VHDL support with
RTL elaboration, hierarchy tree and static elaboration for both languages.  This
is the only configuration for which the Yosys-Verific patch is available.

.. note:: 

   TabbyCAD builds also have additional EDIF and Liberty file support enabled.
   YosysHQ extensions library is only part of TabbyCAD as a product.

.. todo:: is "YosysHQ extensions library" == "YosysHQ specific extensions support" ?

   If not, they need to be better distinguished.  If they are, then how is it
   possible for someone to build the supported configuration?

Partially supported builds
~~~~~~~~~~~~~~~~~~~~~~~~~~

To be able to compile Yosys with Verific, the Verific library must have support
for at least one HDL language with RTL elaboration enabled.  The following table
lists a series of build configurations which are possible, but only provide a
limited subset of features.  Please note that support is limited without YosysHQ
specific extensions of Verific library.

+--------------------------------------------------------------------------+---------------+------+-----------+--------------------+
|                                                                          | Configuration values beginning with ENABLE_VERIFIC\_  |
+--------------------------------------------------------------------------+---------------+------+-----------+--------------------+
| Features                                                                 | SYSTEMVERILOG | VHDL | HIER_TREE | YOSYSHQ_EXTENSIONS |
+==========================================================================+===============+======+===========+====================+
| SystemVerilog + RTL elaboration                                          |             1 |    0 |         0 |                  0 |
+--------------------------------------------------------------------------+---------------+------+-----------+--------------------+
| VHDL + RTL elaboration                                                   |             0 |    1 |         0 |                  0 |
+--------------------------------------------------------------------------+---------------+------+-----------+--------------------+
| SystemVerilog + VHDL + RTL elaboration                                   |             1 |    1 |         0 |                  0 |
+--------------------------------------------------------------------------+---------------+------+-----------+--------------------+
| SystemVerilog + RTL elaboration + Static elaboration + Hier tree         |             1 |    0 |         1 |                  0 |
+--------------------------------------------------------------------------+---------------+------+-----------+--------------------+
| VHDL + RTL elaboration + Static elaboration + Hier tree                  |             0 |    1 |         1 |                  0 |
+--------------------------------------------------------------------------+---------------+------+-----------+--------------------+
| SystemVerilog + VHDL + RTL elaboration + Static elaboration + Hier tree  |             1 |    1 |         1 |                  0 |
+--------------------------------------------------------------------------+---------------+------+-----------+--------------------+

.. note::

   In case your Verific build has EDIF and/or Liberty support, you can enable
   those options. These are not mentioned above for simplification and since
   they are disabled by default.

Verific Features that should be enabled in your Verific library
---------------------------------------------------------------

Please be aware that the following Verific configuration build parameter needs
to be enabled in order to create the fully supported build.

::

   database/DBCompileFlags.h:
       DB_PRESERVE_INITIAL_VALUE
