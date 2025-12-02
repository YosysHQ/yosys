Contributing to Yosys
=====================

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


Reporting bugs
--------------

A good bug report includes the following information:


Title
~~~~~

briefly describe the issue, for example:

   techmap of wide mux with undefined inputs raises error during synth_xilinx

   + tells us what's happening ("raises error")
   + gives the command affected (`techmap`)
   + an overview of the input design ("wide mux with undefined inputs")
   + and some context where it was found ("during `synth_xilinx`")


Reproduction Steps
~~~~~~~~~~~~~~~~~~

The reproduction steps should be a minimal, complete and verifiable
example `MVCE`_.
Providing an MVCE with your bug report drastically increases the likelihood that
someone will be able to help resolve your issue.
One way to minimize a design is to use the `bugpoint_` command.
You can learn more in the `how-to guide for bugpoint_`.

The reproduction steps are ideally a code-block (starting and ending with
triple backquotes) containing
the minimized design (Verilog or RTLIL), followed by a code-block containing
the minimized yosys script OR a command line call to yosys with
code-formatting (starting and ending with single backquotes).

.. code-block:: markdown

   min.v
   ```verilog
   // minimized Verilog design
   ```

   min.ys
   ```
   read_verilog min.v
   # minimum sequence of commands to reproduce error
   ```

   OR

   `yosys -p ': minimum sequence of commands;' min.v`

Alternatively, you can provide a single code-block which includes the minimized
design as a "here document" followed by the sequence of commands which
reproduce the error

  + see :doc:`/using_yosys/more_scripting/load_design` for more on heredocs.

.. code-block:: markdown

   ```
   read_rtlil <<EOF
   # minimized RTLIL design
   EOF
   # minimum sequence of commands
   ```

Don't forget to mention:

- any important environment variables or command line options
- if the problem occurs for a range of values/designs, what is that range
- if you're using an external tool, such as ``valgrind``, to detect the issue,
  what version of that tool are you using and what options are you giving it

.. warning::

   Please try to avoid the use of any external plugins/tools in the reproduction
   steps if they are not directly related to the issue being raised.  This
   includes frontend plugins such as GHDL or slang; use `write_rtlil` on the
   minimized design instead.  This also includes tools which provide a wrapper
   around Yosys such as OpenLane; you should instead minimize your input and
   reproduction steps to just the Yosys part.

.. _MVCE: https://stackoverflow.com/help/minimal-reproducible-example
.. _bugpoint: https://yosys.readthedocs.io/en/latest/cmd/bugpoint.html
.. _how-to guide for bugpoint: https://yosys.readthedocs.io/en/latest/using_yosys/bugpoint.html

Expected Behaviour
~~~~~~~~~~~~~~~~~~

Describe what you'd expect to happen when we follow the reproduction steps
if the bug was fixed.

If you have a similar design/script that doesn't give the error, include it
here as a reference. If the bug is that an error *should* be raised but isn't,
note if there are any other commands with similar error messages.


Actual Behaviour
~~~~~~~~~~~~~~~~

Describe what you actually see when you follow the reproduction steps.

This can include:
- any error messages
- any details relevant to the crash that were found with ``--trace`` or
  ``--debug`` flags
- the part of the source code that triggers the bug
  + if possible, use a permalink to the source on GitHub
  + you can browse the source repository for a certain commit with the failure
    and open the source file, select the relevant lines (click on the line
    number for the first relevant line, then while holding shift click on the
    line number for the last relevant line), click on the ``...`` that appears
    and select "Copy permalink"
  + should look something like
    ``https://github.com/YosysHQ/yosys/blob/<commit_hash>/path/to/file#L139-L147``
  + clicking on "Preview" should reveal a code block containing the lines of
    source specified, with a link to the source file at the given commit


Additional Details
~~~~~~~~~~~~~~~~~~

Anything else you think might be helpful or relevant when verifying or fixing
the bug.

Once you have created the issue, any additional details can be added as a
comment on that issue. You can include any additional context as to what you
were doing when you first encountered the bug.

If this issue discovered through the use of a fuzzer, ALWAYS declare that.
If you've minimized the script, consider including the `bugpoint` script you
used, or the original script, for example:

.. code-block:: markdown

   Minimized with
   ```
   read_verilog design.v
   # original sequence of commands prior to error
   bugpoint -script <failure.ys> -grep "<string>"
   write_rtlil min.il
   ```

   OR

   Minimized from
   `yosys -p ': original sequence of commands to produce error;' design.v`

If possible, it may also help to share the original un-minimized design.
If the design is too big for a comment, consider turning it into a `Gist`_

.. _Gist: https://gist.github.com/
