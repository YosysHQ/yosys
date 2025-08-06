Minimizing failing (or bugged) designs
======================================

.. TODO:: pending merge of https://github.com/YosysHQ/yosys/pull/5068

This document is a how-to guide for reducing problematic designs to the bare
minimum needed for reproducing the issue.  This is a Yosys specific alternative
to the Stack Overflow article: `How to create a Minimal, Reproducible Example`_,
and is intended to help when there's something wrong with your design, or with
Yosys itself.

.. _How to create a Minimal, Reproducible Example: https://stackoverflow.com/help/minimal-reproducible-example

.. note::

   This guide assumes a moderate degree of familiarity with Yosys and requires
   some amount of problem solving ability.


Before you start
----------------

The first (and often overlooked) step, is to check for and *read* any error
messages or warnings.  Passing the ``-q`` flag when running Yosys will make it
so that only warnings and error messages are written to the console.  Don't just
read the last message either, there may be warnings that indicate a problem
before it happens.  While some things may only be regarded as warnings, such as
multiple drivers for the same signal or logic loops, these can cause problems in
some synthesis flows but not others.

A Yosys error (one that starts with ``ERROR:``) may give you a line number from
your design, or the name of the object causing issues.  If so, you may already
have enough information to resolve the problem, or at least understand why it's
happening.

.. note::

   If you're not already, try using the latest version from the `Yosys GitHub`_.
   You may find that your issue has already been fixed!  And even if it isn't,
   testing with two different versions is a good way to ensure reproducibility.

.. _Yosys GitHub: https://github.com/YosysHQ/yosys

Another thing to be aware of is that Yosys generally doesn't perform rigorous
checking of input designs to ensure they are valid.  This is especially true for
the `read_verilog` frontend.  It is instead recommended that you try load it
with `iverilog`_ or `verilator`_ first, as an invalid design can often lead to
unexpected issues.

.. _iverilog: https://steveicarus.github.io/iverilog/
.. _verilator: https://www.veripool.org/verilator/

If you're using a custom synthesis script, try take a bit of time to figure out
which command is failing.  Calling ``echo on`` at the start of your script will
`echo` each command executed; the last echo before the error should then be
where the error has come from.  Check the help message for the failing command;
does it indicate limited support, or mention some other command that needs to be
run first?  You can also try to call `check` and/or ``hierarchy -check`` before
the failure to see if they report and errors or warnings.


Minimizing RTLIL designs with bugpoint
--------------------------------------

Yosys provides the `bugpoint` command for reducing a failing design to the
smallest portion of that design which still results in failure.  While initially
developed for Yosys crashes, `bugpoint` can also be used for designs that lead
to non-fatal errors, or even failures in other tools that use the output of a
Yosys script.

.. note::

   Make sure to back up your code (design source and yosys script(s)) before
   making any modifications.  Even if the code itself isn't important, this can
   help avoid "losing" the error while trying to debug it.

Can I use bugpoint?
~~~~~~~~~~~~~~~~~~~

The first thing to be aware of is that `bugpoint` is not available in every
build of Yosys.  Because the command works by invoking external processes, it
requires that Yosys can spawn executables.  Notably this means `bugpoint` is not
able to be used in WebAssembly builds such as that available via YoWASP.  The
easiest way to check your build of Yosys is by running ``yosys -h bugpoint``. If
Yosys displays the help text for `bugpoint` then it is available for use.

.. code-block:: console
   :caption: `bugpoint` is unavailable

   $ yosys -h bugpoint

   -- Running command `help bugpoint' --
   No such command or cell type: bugpoint

Next you need to separate loading the design from the failure point; you should
be aiming to reproduce the failure by running ``yosys -s <load.ys> -s
<failure.ys>``.  If the failure occurs while loading the design, such as during
`read_verilog` you will instead have to minimize the input design yourself.
Check out the instructions for :ref:`using_yosys/bugpoint:minimizing verilog
designs` below.

.. note::

   You should also be able to run the two scripts separately, calling first
   ``yosys -s <load.ys> -p 'write_rtlil design.il'`` and then ``yosys -s
   <failure.ys> design.il``.  If this doesn't work then it may mean that the
   failure isn't reproducible from RTLIL and `bugpoint` won't work either.

When we talk about failure points here, it doesn't just mean crashes or errors
in Yosys.  The ``<failure.ys>`` script can also be a user-defined failure such
as the `select` command with one of the ``-assert-*`` options; an example where
this might be useful is when a pass is supposed to remove a certain kind of
cell, but there is some edge case where the cell is not removed.  Another
use-case would be minimizing a design which fails with the `equiv_opt` command,
suggesting that the optimization in question alters the circuit in some way.

It is even possible to use `bugpoint` with failures *external* to Yosys, by
making use of the `exec` command in ``<failure.ys>``.  This is especially useful
when Yosys is outputting an invalid design, or when some other tool is
incompatible with the design.  Be sure to use the ``exec -expect-*`` options so
that the pass/fail can be detected correctly.  Multiple calls to `exec` can be
made, or even entire shell scripts:

.. code-block:: yoscrypt

   exec -expect-return 1 --bash <script.sh>

Our final failure we can use with `bugpoint` is one returned by a wrapper
process, such as ``valgrind`` or ``timeout``.  In this case you will be calling
something like ``<wrapper> yosys -s <failure.ys> design.il``.  Here, Yosys is
run under a wrapper process which checks for some failure state, like a memory
leak or excessive runtime.


How do I use bugpoint?
~~~~~~~~~~~~~~~~~~~~~~

At this point you should have:

1. either an RTLIL file containing the design to minimize (referred to here as
   ``design.il``), or a Yosys script, ``<load.ys>``, which loads it; and
2. a Yosys script, ``<failure.ys>``, which produces the failure and returns a
   non-zero return status.

Now call ``yosys -qq -s <failure.ys> design.il`` and take note of the error(s)
that get printed.  A template script, ``<bugpoint.ys>``, is provided here which
you can use.  Make sure to configure it with the correct filenames and use only
one of the methods to load the design.  Fill in the ``-grep`` option with the
error message printed just before.  If you are using a wrapper process for your
failure state, add the ``-runner "<wrapper>"`` option to the `bugpoint` call.

.. code-block:: yoscrypt
   :caption: ``<bugpoint.ys>`` template script

   # Load design
   read_rtlil design.il
   ## OR
   script <load.ys>

   # Call bugpoint with failure
   bugpoint -script <failure.ys> -grep "<string>"

   # Save minimized design
   write_rtlil min.il

The ``-grep`` option is used to search the log file generated by the Yosys under
test.  If the error message is generated by something else, such as a wrapper
process or compiler sanitizer, then you should instead use ``-err_grep``.  For
an OS error, like a SEGFAULT, you can also use ``-expect-return`` to check the
error code returned.

.. note::

   Checking the error message or return status is optional, but highly
   recommended.  `bugpoint` can quite easily introduce bugs by creating
   malformed designs that commands were not intended to handle.  By having some
   way to check the error, `bugpoint` can ensure that it is the *right* error
   being reproduced.  This is even more important when ``<failure.ys>`` contains
   more than one command.

By default, `bugpoint` is able to remove any part of the design.  In order to
keep certain parts, for instance because you already know they are related to
the failure, you can use the ``bugpoint_keep`` attribute.  This can be done with
``(* bugpoint_keep *)`` in Verilog, ``attribute \bugpoint_keep 1`` in RTLIL, or
``setattr -set bugpoint_keep 1 [selection]`` from a Yosys script.  It is also
possible to limit `bugpoint` to only removing certain *kinds* of objects, such
as only removing entire modules or cells (instances of modules).  For more about
the options available, check ``help bugpoint`` or :cmd:title:`bugpoint`.

In some situations, it may also be helpful to use `setenv` before `bugpoint` to
set environment variables for the spawned processes.  An example of this is
``setenv UBSAN_OPTIONS halt_on_error=1`` for where you are trying to raise an
error on undefined behaviour but only want the child process to halt on error.

.. note::

   Using `setenv` in this way may or may not affect the current process.  For
   instance the ``UBSAN_OPTIONS halt_on_error`` here only affects child
   processes, as does the :doc:`Yosys environment variable</appendix/env_vars>`
   ``ABC`` because they are only read on start-up.  While others, such as
   ``YOSYS_NOVERIFIC`` and ``HOME``, are evaluated each time they are used.

Once you have finished configuration, you can now run ``yosys <bugpoint.ys>``.
The first thing `bugpoint` will do is test the input design fails.  If it
doesn't, make sure you are using the right ``yosys`` executable; unless the
``-yosys`` option is provided, it will use whatever the shell defaults to, *not*
the current ``yosys``.  If you are using the ``-runner`` option, try replacing
the `bugpoint` command with ``write_rtlil test.il`` and then on a new line,
``!<wrapper> yosys -s <failure.ys> test.il`` to check it works as expected and
returns a non-zero status.

.. seealso::

   For more on script parsing and the use of ``!``, check out
   :ref:`getting_started/scripting_intro:script parsing`.

Depending on the size of your design, and the length of your ``<failure.ys>``,
`bugpoint` may take some time; remember, it will run ``yosys -s <failure.ys>``
on each iteration of the design.  The bigger the design, the more iterations.
The longer the ``<failure.ys>``, the longer each iteration will take.  As the
design shrinks and `bugpoint` converges, each iteration should take less and
less time.  Once all simplifications are exhausted and there are no more objects
that can be removed, the script will continue and the minimized design can be
saved.


What do I do with the minimized design?
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

First off, check the minimized design still fails.  This is especially important
if you're not using `write_rtlil` to output the minimized design.  For example,
if you ran :ref:`bugpoint_script` below, then calling ``yosys -s <failure.ys>
min.v`` should still fail in the same way.

.. code-block:: yoscrypt
   :caption: example `bugpoint` minimizer
   :name: bugpoint_script

   read_verilog design.v
   bugpoint -script <failure.ys>
   write_verilog min.v

The `write_rtlil` command is generally more reliable, since `bugpoint` will have
run that exact code through the failing script.  Other ``write_*`` commands
convert from the RTLIL and then back again during the ``read_*`` which can
result in differences which mean the design no longer fails.

.. note::

   Simply calling Yosys with the output of ``write_*``, as in ``yosys -s
   <failure.ys> min.v``, does not guarantee that the corresponding ``read_*``
   will be used. For more about this, refer to
   :doc:`/using_yosys/more_scripting/load_design`, or load the design explicitly
   with ``yosys -p 'read_verilog min.v' -s <failure.ys>``.

Once you've verified the failure still happens, check out
:ref:`using_yosys/bugpoint:identifying issues` for more on what to do next.


Minimizing Verilog designs
--------------------------

.. seealso::

   This section is not specific to Yosys, so feel free to use another guide such
   as Stack Overflow's `How to create a Minimal, Reproducible Example`_.

Be sure to check any errors or warnings for messages that might identify source
lines or object names that might be causing the failure, and back up your source
code before modifying it.  If you have multiple source files, you should start
by reducing them down to a single file.  If a specific file is failing to read,
try removing everything else and just focus on that one.  If your source uses
the ``include`` directive, replace it with the contents of the file referenced.

Unlike RTLIL designs where we can use `bugpoint`, Yosys does not provide any
tools for minimizing Verilog designs.  Instead, you should use an external tool
like `C-Reduce`_ (with the ``--not-c`` flag) or `sv-bugpoint`_.

.. _C-Reduce: https://github.com/csmith-project/creduce
.. _sv-bugpoint: https://github.com/antmicro/sv-bugpoint

C-Reduce
~~~~~~~~

As a very brief overview for using C-Reduce, you want your failing source design
(``test.v``), and some shell script which checks for the error being
investigated (``test.sh``).  Below is an :ref:`egtest` which uses `logger` and
the ``-expect error "<string>" 1`` option to perform a similar role to
``bugpoint -grep``, along with ``verilator`` to lint the code and make sure it
is still valid.

.. code-block:: bash
   :caption: Example test.sh for C-Reduce
   :name: egtest

   #!/bin/bash
   verilator --lint-only test.v &&/
   yosys -p 'logger -expect error "unsupported" 1; read_verilog test.v'

.. code-block:: verilog
   :caption: input test.v

   module top(input clk, a, b, c, output x, y, z);
      always @(posedge clk) begin
         if (a == 1'b1)
            $stop;
      end
      assign x = a;
      assign y = a ^ b;
      assign z = c;
   endmodule

In this example ``read_verilog test.v`` is giving an error message that contains
the string "unsupported" because the ``$stop`` system task is only supported in
``initial`` blocks.  By calling ``creduce ./test.sh test.v --not-c`` we can
minimize the design to just the failing code, while still being valid Verilog.

.. code-block:: verilog
   :caption: output test.v

   module a;
   always begin $stop;
   end endmodule


sv-bugpoint
~~~~~~~~~~~

sv-bugpoint works quite similarly to C-Reduce, except it requires an output
directory to be provided and the check script needs to accept the target file as
an input argument: ``sv-bugpoint outDir/ test.sh test.v``

.. code-block:: bash
   :caption: Example test.sh for sv-bugpoint

   #!/bin/bash
   verilator --lint-only $1 &&/
   yosys -p "logger -expect error \"unsupported\" 1; read_verilog $1"

Notice that the commands for ``yosys -p`` are now in double quotes (``"``), and
the quotes around the error string are escaped (``\"``).  This is necessary for
the ``$1`` argument subsitution to work correctly.


Doing it manually
~~~~~~~~~~~~~~~~~

If for some reason you are unable to use a tool to minimize your code, you can
still do it manually.  But it can be a time consuming process and requires a lot
of iteration.  At any point in the process, you can check for anything that is
unused or totally disconnected (ports, wires, etc) and remove them. If a
specific module is causing the problem, try to set that as the top module
instead.  Any parameters should have their default values changed to match the
failing usage.

As a rule of thumb, try to split things roughly in half at each step; similar to
a "binary search".  If you have 10 cells (instances of modules) in your top
module, and have no idea what is causing the issue, split them into two groups
of 5 cells.  For each group of cells, try remove them and see if the failure
still happens.  If the error still occurs with the first group removed, but
disappears when the second group is removed, then the first group can be safely
removed.  If a module has no more instances, remove it entirely.  Repeat this
for each remaining group of cells until each group only has 1 cell in it and no
more cells can be removed without making the error disappear.  You can also
repeat this for each module still in your design.

After minimizing the number of cells, do the same for the process blocks in your
top module.  And again for any generate blocks and combinational blocks.
Remember to check for any ports or signals which are no longer used and remove
those too.  Any signals which are written but never read can also be removed.

.. note::

   Depending on where the design is failing, there are some commands which may
   help in identifying unused objects in the design.  `hierarchy` will identify
   which modules are used and which are not, but check for ``$paramod`` modules
   before removing unused ones. ``debug clean`` will list all unused wires in
   each module, as well as unused cells which were automatically generated
   (giving the line number of the source that generated them).  Adding the
   ``-purge`` flag will also include named wires that would normally be ignored
   by `clean`.  Though when there are large numbers of unused wires it is often
   easier to just delete sections of the code and see what happens.

Next, try to remove or reduce assignments (``a = b``) and operations (``a +
b``).  A good place to start is by checking for any wires/registers which are
read but never written.  Try removing the signal declaration and replacing
references to it with ``'0`` or ``'x``.  Do this with any constants too.  Try to
replace strings with numeric values, and wide signals with smaller ones, then
see if the error persists.

Check if there are any operations that you can simplify, like replacing ``a &
'0`` with ``'0``.  If you have enable or reset logic, try removing it and see if
the error still occurs.  Try reducing ``if .. else`` and ``case`` blocks to a
single case.  Even if that doesn't work, you may still be able to remove some
paths; start with cases that appear to be unreachable and go from there.

.. note::

   When sharing code on the `Yosys GitHub`_, please try to keep things in
   English.  Declarations and strings should stick to the letters a-z and
   numbers 0-9, unless the error is arising because of the names/characters
   used.


Identifying issues
------------------

When identifying issues, it is quite useful to understand the conditions under
which the issue is occurring.  While there are occasionally bugs that affect a
significant number of designs, Yosys changes are tested on a variety of designs
and operating systems which typically catch any such issues before they make it
into the main branch.  So what is is it about your situation that makes it
unusual?

.. note::

   If you have access to a different platform you could also check if your issue
   is reproducible there.  Some issues may be specific to the platform or build
   of Yosys.

Try to match the minimized design back to its original context.  Could you
achieve the same thing a different way, and if so, does this other method have
the same issue?  Try to change the design in small ways and see what happens;
while `bugpoint` can reduce and simplify a design, it doesn't *change* much.
What happens if you change operators, for example a left shift (or `$shl`) to a
right shift (or `$shr`)?  Try to see if the issue is tied to specific
parameters, widths, or values.

Search `the existing issues`_ and see if someone has already made a bug report.
This is where changing the design and finding the limits of what causes the
failure really comes in handy.  If you're more familiar with how the problem can
arise, you may be able to find a related issue more easily.  If an issue already
exists for one case of the problem but you've found other cases, you can comment
on the issue and help get it solved.  If there are no existing or related issues
already, then check out the steps for
:ref:`yosys_internals/extending_yosys/contributing:reporting bugs`.

.. _the existing issues: https://github.com/YosysHQ/yosys/issues

.. warning::

   If you are using a fuzzer to find bugs, follow the instructions for
   :doc:`/yosys_internals/extending_yosys/advanced_bugpoint`.  **Do not** open
   more than one fuzzer generated issue at a time if you can not identify the
   root cause.  If you are found to be doing this, your issues may be closed
   without further investigation.
