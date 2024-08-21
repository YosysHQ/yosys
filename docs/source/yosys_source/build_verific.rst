Compiling with Verific library
==============================

YosysHQ creates build for TabbyCAD Suite that includes Verific with additional
patches and our own extensions library. However, if you have licensed Verific
library in source or binary form you can still compile Yosys and have at least
partial support.

Compile options
---------------

To enable Verific support ``ENABLE_VERIFIC`` has to be set to ``1`` and
``VERIFIC_DIR`` needs to point to location where library is located.

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
---------------

Default options values are created in such way to represent supported build.
This one includes SystemVerilog and VHDL support with RTL elaboration, hierarchy
tree and static elaboration for both languages.

Fully supported build includes additional YosysHQ patch that can be bought for
**only** this Verific library configuration.

NOTE: TabbyCAD builds also have additional EDIF and Liberty file support enabled
as well. YosysHQ extensions library is only part of TabbyCAD as a product.

Partialy supported builds
-------------------------

Note that these builds can be used with Yosys but will miss some of important
features.

1. SystemVerilog + RTL elaboration

================================= =======
Parameter                         Default
================================= =======
ENABLE_VERIFIC_SYSTEMVERILOG      1
ENABLE_VERIFIC_VHDL               0
ENABLE_VERIFIC_HIER_TREE          0
ENABLE_VERIFIC_YOSYSHQ_EXTENSIONS 0
================================= =======

2. VHDL + RTL elaboration

================================= =======
Parameter                         Default
================================= =======
ENABLE_VERIFIC_SYSTEMVERILOG      0
ENABLE_VERIFIC_VHDL               1
ENABLE_VERIFIC_HIER_TREE          0
ENABLE_VERIFIC_YOSYSHQ_EXTENSIONS 0
================================= =======

3. SystemVerilog + VHDL + RTL elaboration

================================= =======
Parameter                         Default
================================= =======
ENABLE_VERIFIC_SYSTEMVERILOG      1
ENABLE_VERIFIC_VHDL               1
ENABLE_VERIFIC_HIER_TREE          0
ENABLE_VERIFIC_YOSYSHQ_EXTENSIONS 0
================================= =======

3. SystemVerilog + RTL elaboration + Static elaboration + Hier tree

================================= =======
Parameter                         Default
================================= =======
ENABLE_VERIFIC_SYSTEMVERILOG      1
ENABLE_VERIFIC_VHDL               0
ENABLE_VERIFIC_HIER_TREE          1
ENABLE_VERIFIC_YOSYSHQ_EXTENSIONS 0
================================= =======

3. VHDL + RTL elaboration + Static elaboration + Hier tree

================================= =======
Parameter                         Default
================================= =======
ENABLE_VERIFIC_SYSTEMVERILOG      0
ENABLE_VERIFIC_VHDL               1
ENABLE_VERIFIC_HIER_TREE          1
ENABLE_VERIFIC_YOSYSHQ_EXTENSIONS 0
================================= =======

4. SystemVerilog + VHDL + RTL elaboration + Static elaboration + Hier
   tree

================================= =======
Parameter                         Default
================================= =======
ENABLE_VERIFIC_SYSTEMVERILOG      1
ENABLE_VERIFIC_VHDL               1
ENABLE_VERIFIC_HIER_TREE          1
ENABLE_VERIFIC_YOSYSHQ_EXTENSIONS 0
================================= =======

NOTE:

In case your Verific build have EDIF and/or Liberty support, you can enable
those options, these are not mentioned above for simplification and since they
are disabled by default.

NOTE: To be able to compile Yosys+Verific you need Verific library that have at
least one of HDL languages support with RTL elaboration enabled. Please note
that without YosysHQ specific extensions of Verific library, support is limited.

Verific Features that should be enabled in your Verific library
===============================================================

Please be aware that next Verific configuration build parameter needs to be
enabled in order to create fully supported build.

::

   database/DBCompileFlags.h:
       DB_PRESERVE_INITIAL_VALUE

Additional features included with Yosys Verific patch
=====================================================

New cells
---------

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
