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
