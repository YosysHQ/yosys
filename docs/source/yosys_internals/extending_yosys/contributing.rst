Contributing to Yosys
=====================

.. note::

   For information on making a pull request on github, refer to our
   |CONTRIBUTING|_ file.

.. |CONTRIBUTING| replace:: :file:`CONTRIBUTING.md`
.. _CONTRIBUTING: https://github.com/YosysHQ/yosys/blob/main/CONTRIBUTING.md

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

- use the `bug report template`_

.. _bug report template: https://github.com/YosysHQ/yosys/issues/new?template=bug_report.yml

- short title briefly describing the issue, e.g.

   techmap of wide mux with undefined inputs raises error during synth_xilinx

   + tells us what's happening ("raises error")
   + gives the command affected (`techmap`)
   + an overview of the input design ("wide mux with undefined inputs")
   + and some context where it was found ("during `synth_xilinx`")


Reproduction Steps
~~~~~~~~~~~~~~~~~~

- ideally a code-block (starting and ending with triple backquotes) containing
  the minimized design (Verilog or RTLIL), followed by a code-block containing
  the minimized yosys script OR a command line call to yosys with
  code-formatting (starting and ending with single backquotes)

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

- alternatively can provide a single code-block which includes the minimized
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

- any environment variables or command line options should also be mentioned
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

"Expected Behaviour"
~~~~~~~~~~~~~~~~~~~~

- if you have a similar design/script that doesn't give the error, include it
  here as a reference
- if the bug is that an error *should* be raised but isn't, are there any other
  commands with similar error messages


"Actual Behaviour"
~~~~~~~~~~~~~~~~~~

- any error messages go here
- any details relevant to the crash that were found with ``--trace`` or
  ``--debug`` flags
- if you identified the point of failure in the source code, you could mention
  it here, or as a comment below

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


Additional details
~~~~~~~~~~~~~~~~~~

- once you have created the issue, any additional details can be added as a
  comment on that issue
- could include any additional context as to what you were doing when you first
  encountered the bug
- was this issue discovered through the use of a fuzzer
- if you've minimized the script, consider including the `bugpoint` script you
  used, or the original script, e.g.

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

- if you're able to, it may also help to share the original un-minimized design

  + if the design is too big for a comment, consider turning it into a `Gist`_

.. _Gist: https://gist.github.com/
