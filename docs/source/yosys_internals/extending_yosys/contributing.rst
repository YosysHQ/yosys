Contributing to Yosys
=====================

.. note::

   For information on making a pull request on github, refer to our
   |CONTRIBUTING|_ file.

.. |CONTRIBUTING| replace:: :file:`CONTRIBUTING.md`
.. _CONTRIBUTING: https://github.com/YosysHQ/yosys/CONTRIBUTING.md

Coding Style
------------

Formatting of code
~~~~~~~~~~~~~~~~~~

- Yosys code is using tabs for indentation. Tabs are 8 characters.

- A continuation of a statement in the following line is indented by two
  additional tabs.

- Lines are as long as you want them to be. A good rule of thumb is to break
  lines at about column 150.

- Opening braces can be put on the same or next line as the statement opening
  the block (if, switch, for, while, do). Put the opening brace on its own line
  for larger blocks, especially blocks that contains blank lines.

- Otherwise stick to the `Linux Kernel Coding Style`_.

.. _Linux Kernel Coding Style: https://www.kernel.org/doc/Documentation/process/coding-style.rst


C++ Language
~~~~~~~~~~~~

Yosys is written in C++17.

In general Yosys uses ``int`` instead of ``size_t``. To avoid compiler warnings
for implicit type casts, always use ``GetSize(foobar)`` instead of
``foobar.size()``. (``GetSize()`` is defined in :file:`kernel/yosys.h`)

Use range-based for loops whenever applicable.

Generated help messages and documentation
-----------------------------------------

Command help
~~~~~~~~~~~~

- `help` without arguments

  - lists all commands with their ``Pass::short_help``

- ``help <command>``

  - calls ``Pass::help()`` for ``<command>``

.. note::

   A more expressive way to generate formatted help messages is `in
   development`_.

.. _in development: https://github.com/YosysHQ/yosys/pull/4860

Cell help
~~~~~~~~~

- :file:`techlibs/common/simcells.v` and :file:`techlibs/common/simlib.v`
- parsed by :file:`techlibs/common/cellhelp.py`
- comments preceding cell type converted to a ``SimHelper`` struct, defined in
  :file:`kernel/register.cc`
- ``#include``d in :file:`kernel/register.cc`, creating a map of cell types to
  their ``SimHelper`` struct.

- ``help -cells``

  - lists all cells with their input/output ports

- ``help <celltype>``

  - prints help message for ``<celltype>``
  - constructed from ``SimHelper`` content depending on version

- ``help <celltype>+``

  - prints verilog code for ``<celltype>``

v1 (default)
^^^^^^^^^^^^

- Legacy format
- Expects formatting as follows:

.. code-block:: verilog

   //-
   //-    $<celltype> (<ports>)
   //* group <cellgroup>
   //-
   //- <cell description>
   //-
   module \$<celltype> (<ports>);
   // ...
   endmodule

- ``//* group`` line is generally after the cell signature, but can appear
  anywhere in the comment block

  - determines where the cell is included in sphinx
  - check :file:`docs/source/cell` for current groups
  - a missing group will raise an error
  - assigning an unused group will result in the cell not being included in the
    sphinx docs

- the port signature line (``//-    $<celltype> (<ports>)``) must start with (at
  least) 4 spaces (not tabs)

  - the empty lines (``//-``) before/after the signature are required

- cell description can be multiple lines, but each line must start with ``//-``
  and a space

  - description should have a trailing empty line
  - line breaks are preserved in `help` calls but will be rendered as text in
    sphinx docs, with empty lines being required between paragraphs

- cells in :file:`techlibs/common/simcells.v` can have optional truth table at
  the end of the cell description which is rendered in sphinx docs as a literal
  code block
- e.g. `$_NOT_`:

.. code-block:: verilog

   //-
   //-     $_NOT_ (A, Y)
   //* group comb_simple
   //-
   //- An inverter gate.
   //-
   //- Truth table:    A | Y
   //-                ---+---
   //-                 0 | 1
   //-                 1 | 0
   //-

v2 (more expressive)
^^^^^^^^^^^^^^^^^^^^

- each field of the ``SimHelper`` struct can be assigned with:

.. code-block:: verilog

   //* <name> <value>

- ``ver`` must be explicitly set as ``2``
- optional fields ``title`` and ``tags``

  - title used for better displaying of cell
  - tags is a space-separated list of :doc:`/cell/properties`

- the port signature is automatically generated from the ``module`` definition
- cell description is the same as v1
- can link to commands or passes using backticks (`````)
- e.g. `$nex`:

.. code-block:: verilog

   //* ver 2
   //* title Case inequality
   //* group binary
   //* tags x-aware
   //- This corresponds to the Verilog '!==' operator.
   //-
   //- Refer to `$eqx` for more details.
   //-

- code blocks can be included as following:

.. code-block:: verilog

   //- text
   //- ::
   //-
   //-    monospaced text
   //-
   //-        indentation and line length will be preserved, giving a scroll bar if necessary for the browser window
   //-
   //- more text

- the empty line after the ``::`` and before the text continues are required
- the ``::`` line will be ignored in the `help` call while sphinx docs will
  treat everything that follows as a literal block until the next unindented
  line:

   text
   ::

      monospaced text

         indentation and line length will be preserved, giving a scroll bar if necessary for the browser window

   more text
