Contributing to Yosys
=====================

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

* any error messages
* any details relevant to the crash that were found with ``--trace`` or
  ``--debug`` flags
* the part of the source code that triggers the bug

  * if possible, use a permalink to the source on GitHub
  * you can browse the source repository for a certain commit with the failure
    and open the source file, select the relevant lines (click on the line
    number for the first relevant line, then while holding shift click on the
    line number for the last relevant line), click on the ``...`` that appears
    and select "Copy permalink"
  * should look something like
    ``https://github.com/YosysHQ/yosys/blob/<commit_hash>/path/to/file#L139-L147``
  * clicking on "Preview" should reveal a code block containing the lines of
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

Contributing code
-----------------

Code that matters
~~~~~~~~~~~~~~~~~

If you're adding complex functionality, or modifying core parts of yosys,
we highly recommend discussing your motivation and approach
ahead of time on the `Discourse forum`_.

Before you build or fix something, search for existing `issues`_.

.. _`Discourse forum`: https://yosyshq.discourse.group/
.. _`issues`: https://github.com/YosysHQ/yosys/issues

Making sense
~~~~~~~~~~~~

Given enough effort, the behavior of any code can be figured out to any
desired extent. However, the author of the code is by far in the best
position to make this as easy as possible.

Yosys is a long-standing project and has accumulated a lot of C-style code
that's not written to be read, just written to run. We improve this bit
by bit when opportunities arise, but it is what it is.
New additions are expected to be a lot cleaner.

The purpose and behavior of the code changed should be described clearly.
Your change should contain exactly what it needs to match that description.
This means:

* nothing more than that - no dead code, no undocumented features
* nothing missing - if something is partially built, that's fine,
  but you have to make that clear. For example, some passes
  only support some types of cells

Here are some software engineering approaches that help:

* Use abstraction to model the problem and hide details

  * Maximize the usage of types (structs over loose variables),
    not necessarily in an object-oriented way
  * Use functions, scopes, type aliases

* In new passes, make sure the logic behind how and why it works is actually provided
  in coherent comments, and that variable and type naming is consistent with the terms
  you use in the description.
* The logic of the implementation should be described in mathematical
  or algorithm theory terms. Why would a non-trivial loop be guaranteed to terminate?
  Is there some variant? Are you re-implementing a classic data structure from logic
  synthesis?
* There's various ways of traversing the design with use-def indices (for getting
  drivers and driven signals) available in Yosys. They have advantages and sometimes
  disadvantages. Prefer not re-implementing these
* Prefer references over pointers, and smart pointers over raw pointers
* Aggressively deduplicate code. Within functions, within passes,
  across passes, even against existing code
* Prefer declaring things ``const``
* Prefer range-based for loops over C-style

Common mistakes
~~~~~~~~~~~~~~~

.. - Pointer invalidation when erasing design objects on a module while iterating
.. TODO figure out how it works again and describe it

* Iterating over an entire design and checking if things are selected is more
  inefficient than using the ``selected_*`` methods
* Remember to call ``fixup_ports`` at the end if you're modifying module interfaces

Testing your change
~~~~~~~~~~~~~~~~~~~

Untested code can't be maintained. Inevitable codebase-wide changes
are likely to break anything untested. Tests also help reviewers understand
the purpose of the code change in practice.

Your code needs to come with tests. If it's a feature, a test that covers
representative examples of the added behavior. If it's a bug fix, it should
reproduce the original isolated bug. But in some situations, adding a test
isn't viable. If you can't provide a test, explain this decision.

Prefer writing unit tests (:file:`tests/unit`) for isolated tests to
the internals of more serious code changes, like those to the core of yosys,
or more algorithmic ones.

The rest of the test suite is mostly based on running Yosys on various Yosys
and Tcl scripts that manually call Yosys commands.
See :doc:`/yosys_internals/extending_yosys/test_suites` for more information
about how our test suite is structured.
The basic test writing approach is checking
for the presence of some kind of object or pattern with ``-assert-count`` in
:doc:`/using_yosys/more_scripting/selections`.

It's often best to use equivalence checking with ``equiv_opt -assert``
or similar to prove that the changes done to the design by a modified pass
preserve equivalence. But some code isn't meant to preserve equivalence.
Sometimes proving equivalence takes an impractically long time for larger
inputs. Also beware, the ``equiv_`` passes are a bit quirky and might even
have incorrect results in unusual situations.

.. Changes to core parts of Yosys or passes that are included in synthesis flows
.. can change runtime and memory usage - for the better or for worse. This strongly
.. depends on the design involved. Such risky changes should then be benchmarked
.. with various designs.

.. TODO Emil benchmarking

Coding style
~~~~~~~~~~~~

Yosys is written in C++17.

In general Yosys uses ``int`` instead of ``size_t``. To avoid compiler warnings
for implicit type casts, always use ``GetSize(foobar)`` instead of
``foobar.size()``. (``GetSize()`` is defined in :file:`kernel/yosys.h`)

For auto formatting code, a :file:`.clang-format` file is present top-level.
Yosys code is using tabs for indentation. A tab is 8 characters wide,
but prefer not relying on it. A continuation of a statement
in the following line is indented by two additional tabs. Lines are
as long as you want them to be. A good rule of thumb is to break lines
at about column 150. Opening braces can be put on the same or next line
as the statement opening the block (if, switch, for, while, do).
Put the opening brace on its own line for larger blocks, especially
blocks that contains blank lines. Remove trailing whitespace on sight.

Otherwise stick to the `Linux Kernel Coding Style`_.

.. _Linux Kernel Coding Style: https://www.kernel.org/doc/Documentation/process/coding-style.rst

Git style
~~~~~~~~~

We don't have a strict commit message style.

Some style hints:

* Refactor and document existing code if you touch it,
  but in separate commits from your functional changes
* Prefer smaller commits organized by good chunks. Git has a lot of features
  like fixup commits, interactive rebase with autosquash

.. Reviewing PRs
.. -------------

.. TODO Emil review process
