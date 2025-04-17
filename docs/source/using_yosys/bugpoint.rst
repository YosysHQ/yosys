Minimizing failing (or bugged) designs
======================================

- how to guide
- assumes knowledge and familiarity with Yosys
- something is wrong with your design OR something is wrong with Yosys

  + how to work out which

- *read* the error message
- is it a Yosys error? (starts with ERROR:)

  + does it give you a line number from your design

- is it a runtime error, e.g. SEGFAULT
- are you using the latest release of Yosys

  + has your problem already been fixed

- is your input design valid?

  + if you're using Verilog, try load it with `iverilog`_ or `verilator`_

.. _iverilog: https://steveicarus.github.io/iverilog/
.. _verilator: https://www.veripool.org/verilator/

- make sure to back up your code (design source and yosys script(s)) before
  making any modifications

  + even if the code itself isn't important, this can help avoid "losing" the
    error while trying to debug it


.. _minimize your RTLIL:

Minimizing RTLIL designs with bugpoint
--------------------------------------

Yosys provides the `bugpoint` command for reducing a failing design to the
smallest portion of that design which still results in failure.  While initially
developed for Yosys crashes, `bugpoint` can also be used for designs that lead
to non-fatal errors, or even failures in other tools that use the output of a
Yosys script.

Can I use bugpoint?
~~~~~~~~~~~~~~~~~~~

The first thing to be aware of is that `bugpoint` is not available in every
build of Yosys.  Because the command works by invoking external processes, it
requires that Yosys can spawn executables.  Notably this means `bugpoint` is not
able to be used in WebAssembly builds such as that available via YoWASP.  The
easiest way to check your build of Yosys is by running ``yosys -qq -p '!echo
test'``.  If this echoes ``test`` in the console, then `bugpoint` will work as
expected.  If instead if it displays the text ``ERROR: Shell is not available.``
then `bugpoint` will not work either.

.. note::

   The console command ``yosys -qq -p '!echo test'`` uses the ``-qq`` flag to
   prevent Yosys from outputting non-error messages to the console.  The ``-p``
   option executes ``!echo test`` as a Yosys command, attempting to pass ``echo
   test`` to the shell for execution.  For more about the ``-p`` option and
   common pitfalls, check out :ref:`getting_started/scripting_intro:script
   parsing` in the :doc:`/getting_started/index` section.

.. TODO:: Add ``YOSYS_DISABLE_SPAWN`` check in ``bugpoint.cc``.

   At least in the help text, so that ``yosys -h bugpoint`` will correctly
   indicate if the command will work instead of this roundabout method.

Next you need to separate loading the design from the failure point; you should
be aiming to reproduce the failure by running ``yosys -s <load.ys> -s
<failure.ys>``.  If the failure occurs while loading the design, such as during
`read_verilog` you will instead have to minimize the input design yourself.
Check out the instructions for :ref:`using_yosys/bugpoint:minimizing verilog
designs` below.

The commands in ``<load.ys>`` only need to be run once, while those in
``<failure.ys>`` will be run on each iteration of `bugpoint`.  If you haven't
already, following the instructions for :ref:`using_yosys/bugpoint:minimizing
scripts` will also help with identifying exactly which commands are needed to
produce the failure and which can be safely moved to the loading script.

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
made, or even entire shell scripts (e.g. ``exec -expect-return 1 -- bash
<script.sh>``).

Our final failure we can use with `bugpoint` is one returned by a wrapper
process, such as ``valgrind`` or ``timeout``.  In this case you will be calling
something like ``<wrapper> yosys -s <failure.ys> design.il``.  Here, Yosys is
run under a wrapper process which checks for some failure state, like a memory
leak or excessive runtime.  Note however that unlike the `exec` command, there
is currently no way to check the return status or messages from the wrapper
process; only a binary pass/fail.


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
For more about the options available, check ``help bugpoint`` or
:doc:`/cmd/bugpoint`.

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

.. note::

   Using ``-grep "<string>"`` with `bugpoint` is optional, but helps to ensure
   that the minimized design is reproducing the right error, especially when
   ``<failure.ys>`` contains more than one command.  Unfortunately this does not
   work with runtime errors such as a ``SEGFAULT`` as it is only able to match
   strings from the log file.

.. TODO::  Consider checking ``run_command`` return value for runtime errors.

   Currently ``BugpointPass::run_yosys`` returns ``run_command(yosys_cmdline) ==
   0``, so it shouldn't be too hard to add an option for it.  Could also be
   used with the ``-runner`` option, which might give it a bit more flexibility.

By default, `bugpoint` is able to remove any part of the design.  In order to
keep certain parts, for instance because you already know they are related to
the failure, you can use the ``bugpoint_keep`` attribute.  This can be done with
``(* bugpoint_keep *)`` in Verilog, ``attribute \bugpoint_keep 1`` in RTLIL, or
``setattr -set bugpoint_keep 1 [selection]`` from a Yosys script.  It is also
possible to limit `bugpoint` to only removing certain *kinds* of objects, such
as only removing entire modules or cells (instances of modules).  For more about
the options available, check ``help bugpoint`` or :doc:`/cmd/bugpoint`.

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
``-yosys`` option is provided, it will use whatever the shell defaults to.  If
you are using the ``-runner`` option, try replacing the `bugpoint` command with
``write_rtlil test.il`` and then on a new line, ``!<wrapper> yosys -s
<failure.ys> test.il`` to check it works as expected and returns a non-zero
status.

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


.. _minimize your script:

Minimizing scripts
------------------

If you're using a command line prompt, such as ``yosys -p 'synth_xilinx' -o
design.json design.v``, consider converting it to a script.  It's generally much
easier to iterate over changes to a script in a file rather than one on the
command line, as well as being better for sharing with others.

.. code-block:: yoscrypt
   :caption: example script, ``script.ys``, for prompt ``yosys -p 'synth_xilinx' -o design.json design.v``

   read_verilog design.v
   synth_xilinx
   write_json design.json

Next up you want to remove everything *after* the error occurs.  Using the
``-L`` flag can help here, allowing you to specify a file to log to, such as
``yosys -L out.log -s script.ys``.  Most commands will print a header message
when they begin; something like ``2.48. Executing HIERARCHY pass (managing
design hierarchy).``  The last header message will usually be the failing
command.  There are some commands which don't print a header message, so you may
want to add ``echo on`` to the start of your script.  The `echo` command echoes
each command executed, along with any arguments given to it.  For the
`hierarchy` example above this might be ``yosys> hierarchy -check``.

.. note::

   It may also be helpful to use the `log` command to add messages which you can
   then search for either in the terminal or the logfile.  This can be quite
   useful if your script contains script-passes, like the
   :doc:`/using_yosys/synthesis/synth`, which call many sub-commands and you're
   not sure exactly which script-pass is calling the failing command.

If your final command calls sub-commands, replace it with its contents and
repeat the previous step.  In the case of the
:doc:`/using_yosys/synthesis/synth`, as well as certain other script-passes, you
can use the ``-run`` option to simplify this.  For example we can replace
``synth -top <top> -lut`` with the :ref:`replace_synth`.  The options ``-top
<top> -lut`` can be provided to each `synth` step, or to just the step(s) where
it is relevant, as done here.

.. code-block:: yoscrypt
   :caption: example replacement script for `synth` command
   :name: replace_synth

   synth -top <top> -run :coarse
   synth -lut -run coarse:fine
   synth -lut -run fine:check
   synth -run check:

Say we ran :ref:`replace_synth` and were able to remove the ``synth -run
check:`` and still got our error, then we check the log and we see the last
thing before the error was ``7.2. Executing MEMORY_MAP pass (converting memories
to logic and flip-flops)``. By checking the output of ``yosys -h synth`` (or the
`synth` help page) we can see that the `memory_map` pass is called in the
``fine`` step.  We can then update our script to the following:

.. code-block:: yoscrypt
   :caption: example replacement script for `synth` when `memory_map` is failing

   synth -top <top> -run :fine
   opt -fast -full
   memory_map

By giving `synth` the option ``-run :fine``, we are telling it to run from the
beginning of the script until the ``fine`` step, where we then give it the exact
commands to run.  There are some cases where the commands given in the help
output are not an exact match for what is being run, but are instead a
simplification.  If you find that replacing the script-pass with its contents
causes the error to disappear, or change, try calling the script-pass with
``echo on`` to see exactly what commands are being called and what options are
used.

.. warning::

   Before continuing further, *back up your code*.  The following steps can
   remove context and lead to over-minimizing scripts, hiding underlying issues.
   Check out :ref:`using_yosys/bugpoint:Why context matters` to learn more.

- try ``write_rtlil <design.il>; design -reset; read_rtlil <design.il>;`` before
  the failure point

  + ideally you now have a single command that is producing an error and can
    `minimize your RTLIL`_ with the ``<design.il>`` output
  + if not, try to move the write/reset/read earlier in the script until you can
    reproduce the error
  + if you have no idea where exactly you should put the reset, the best way is
    to use a "binary search" type approach, reducing the possible options by
    half after each attempt

    * for example, your script has 16 commands in it before failing on the 17th
    * if resetting immediately before the 17th doesn't reproduce the error, try
      between the 8th and 9th (8 is half of the total 16)
    * if that produces the error then you can remove everything before the
      `read_rtlil` and try reset again in the middle of what's left, making sure
      to use a different name for the output file so that you don't overwrite
      what you've already got
    * if the error isn't produced then you need to go earlier still, so in this
      case you would do between the 4th and 5th (4 is half of the previous 8)
    * repeat this until you can't reduce the remaining commands any further

.. TODO:: is it possible to dump scratchpad?

   is there anything else in the yosys/design state that doesn't get included in
   `write_rtlil`?

- you can also try to remove or comment out commands prior to the failing
  command; just because the first and last commands are needed doesn't mean that
  every command between them is


Minimizing Verilog designs
--------------------------

- manual process
- made easier if the error message is able to identify the source line or name
  of the object
- reminder to back up original code before modifying it
- if a specific module is causing the problem, try to set that as the top
  module, you can then remove 

  + if the problem is parameter specific you may be able to change the default
    parameters so that they match the problematic configuration

- as with `minimize your script`_, if you have no idea what is or is not
  relevant, try to follow a "binary search" type approach where you remove (or
  comment out) roughly half of what's left at a time
- focusing on one type of object at a time simplifies the process, removing as
  many as you can until the error disappears if any of the remaining objects are
  removed
- periodically check if anything is totally disconnected (ports, wires, etc), if
  it is then it can be removed too
- start by removing cells (instances of modules)

  + if a module has no more instances, remove it entirely

- then processes
- try to remove or reduce assignments and operations

  + are there any wires/registers which get read but never written?

    * try removing the signal declaration and replacing references to it with
      ``'0`` or ``'x``
    * try this with constants too

  + can you replace strings with numeric values?
  + are you able to simplify any operations?  like replacing ``a & '0`` with
    ``'0``
  + if you have enable or reset logic, does the error still happen without that?
  + can you reduce an ``if .. else`` to a single case?

- if you're planning to share the minimized code:

  + make sure there is no sensitive or proprietary data in the design
  + instead of a long string of numbers and letters that had some meaning (or
    were randomly or sequentially generated), can you give it a single character
    name like ``a`` or ``x``
  + please try to keep things in English, using the letters a-z and numbers 0-9
    (unless the error is arising because of the names used)


Identifying issues
------------------

- does the failing command indicate limited support, or does it mention some
  other command that needs to be run first?
- if you're able to, try to match the minimized design back to its original
  context

  + could you achieve the same thing a different way?
  + and if so, does this other method have the same issue?

- try to change the design in small ways and see what happens

  + `bugpoint` can reduce and simplify a design, but it doesn't *change* much
  + what happens if you change operators, for example a left shift (or `$shl`)
    to a right shift (or `$shr`)?
  + is the issue tied to specific parameters, widths, or values?

- if the failing command was part of a larger script, such as one of the
  :doc:`/using_yosys/synthesis/synth`, you could try to follow the design
  through the script

  + sometimes when a command is raising an error, you're seeing a symptom rather
    than the underlying issue
  + an earlier command may be putting the design in an invalid state which isn't
    picked up until the error is raised
  + check out :ref:`using_yosys/bugpoint:Why context matters`
  + if you're using a fuzzer to find issues in Yosys, you should be prepared to
    do this step

- if you're familiar with C/C++ you might try to have a look at the source
  code of the command that's failing

  + even if you can't fix the problem yourself, it can be very helpful for
    anyone else investigating if you're able to identify where exactly the
    issue is
  + if you're using a fuzzer to find issues in Yosys, you should be prepared to
    do this step

.. warning::

   In the event that you are unable to identify the root cause of a fuzzer
   generated issue, **do not** open more than one issue at a time.  You have no
   way of being able to tell if multiple fuzzer generated issues are simply
   different cases of the same problem, and opening multiple issues for the same
   problem means more time is spent on triaging and diagnosing bug reports and
   less on fixing the problem.  If you are found to be doing this, your issues
   may be closed without further investigation.

- search `the existing issues`_ and see if someone has already made a bug report

  + this is where changing the design and finding the limits of what causes the
    failure really comes in handy
  + if you're more familiar with how the problem can arise, you may be able to
    find a related issue more easily
  + if an issue already exists for one case of the problem but you've found
    other cases, you can comment on the issue and help get it solved

.. _the existing issues: https://github.com/YosysHQ/yosys/issues

- if there are no existing or related issues already, then check out the steps
  for :ref:`using_yosys/bugpoint:creating an issue on github`


Why context matters
-------------------

- if you did `minimize your script`_, and removed commands prior to the failure
  to get a smaller design, try to work backwards and find which commands may
  have contributed to the design failing
- especially important when the bug is happening inside of a ``synth_*`` script
- example (#4590)
  
  + say you did all the minimization and found that the error occurs when a call
    to ``techmap -map +/xilinx/cells_map.v`` with ``MIN_MUX_INPUTS`` defined
    parses a `$_MUX16_` with all inputs set to ``1'x``
  + step through the original script, calling `stat` after each step to find
    when the `$_MUX16_` is added
  + find that the `$_MUX16_` is introduced by a call to `muxcover`, but all the
    inputs are defined, so calling `techmap` now works as expected

    * and from running `bugpoint` with the failing techmap you know that the
      cell with index ``2297`` will fail, so you can now call ``select
      top/*$2297`` to limit to just that cell, and optionally call ``design
      -save pre_bug`` or ``write_rtlil -selected pre_bug.il`` to save this state

  + next you step through the remaining commands and call `dump` after each to
    find when the inputs are disconnected
  + find that ``opt -full`` has optimized away portions of the circuit, leading
    to `opt_expr` setting the undriven mux inputs to ``x``, but failing to
    remove the now unnecessary `$_MUX16_`

- in this example, you might've stopped with the minimal reproducer, fixed the
  bug in ``+/xilinx/cells_map.v``, and carried on
- but by following the failure back you've managed to identify a problem with
  `opt_expr` that could be causing other problems either now or in the future


Creating an issue on GitHub
---------------------------

- "Reproduction Steps" is ideally a code-block (starting and ending with triple
  backquotes) containing the minimized design (Verilog or RTLIL), followed by a
  code-block containing the minimized yosys script OR a command line call to
  yosys with code-formatting (starting and ending with single backquotes)

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

- any environment variables or command line options should also be mentioned in
  the "Reproduction Steps"
