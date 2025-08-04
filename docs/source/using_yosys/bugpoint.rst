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

- what is `bugpoint`

Can I use bugpoint?
~~~~~~~~~~~~~~~~~~~

- `bugpoint`, only usable on platforms where Yosys can spawn executables

  + unavailable on emscripten and wasm
  + can test by running e.g. ``yosys -qqp '!echo test'``

    * the ``-qq`` prevents Yosys from outputting non-error messages to the
      console, so this will either display the text ``test``, or an error
      message about ``Shell`` being unavailable
    * check :ref:`getting_started/scripting_intro:script parsing` for more about
      the ``-p`` option and common pitfalls

- single command (``yosys -p '<command>' design.il``)
- *or* multiple commands in a separate script file

  + script shouldn't load the design
  + ``yosys -s <failure.ys> design.il``
  + `minimize your script`_ to reduce the time needed by `bugpoint`

- doesn't require design to be in RTLIL format

  + can e.g. ``read_verilog <design.v>; prep -top <top>;`` before `bugpoint`
  + this method may be more useful if you are trying to find a bug in your
    design rather than Yosys
  + but, `bugpoint` itself calls the command/script with an RTLIL dump, so if it
    isn't reproducible from RTLIL then `bugpoint` won't work


How do I use bugpoint?
~~~~~~~~~~~~~~~~~~~~~~

- follow `bugpoint` instructions
- output design after `bugpoint` with `write_rtlil`
- use ``-grep "<string>"`` to only accept a minimized design that crashes
- with the ``<string>`` in the log file

  + only checks log file, will not match runtime errors

- ``-modules``, ``-ports``, ``-cells``, and ``-processes`` will enable those
- parts of the design to be removed (default is allow removing all)

  + use the ``bugpoint_keep`` attribute on objects you don't want to be
    removed, usually because you already know they are related to the failure
  + ``(* bugpoint_keep *)`` in Verilog, ``attribute \bugpoint_keep 1`` in
    RTLIL, or ``setattr -set bugpoint_keep 1 [selection]`` from script

- ``-runner "<prefix>"`` can allow running ``yosys`` wrapped by another
- command
- can also use `setenv` before `bugpoint` to set environment variables for
- the spawned processes (e.g. ``setenv UBSAN_OPTIONS halt_on_error=1``)

.. note::

   Using `setenv` in this way may not affect the current process as some
   environment variables are only read on start up.  For instance the
   ``UBSAN_OPTIONS halt_on_error`` here only affects child processes, as does
   the :doc:`Yosys environment variable</appendix/env_vars>` ``ABC``.  While
   others such as ``YOSYS_NOVERIFIC`` and ``HOME`` are evaluated each time they
   are used.


What do I do with the minimized design?
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

- check minimized design still fails, especially if not using `write_rtlil`
- e.g. if you ran :ref:`bugpoint_script` below, then calling ``yosys -s
  <failure.ys> min.v`` should still fail in the same way

.. code-block:: yoscrypt
   :caption: example `bugpoint` minimizer
   :name: bugpoint_script

   read_verilog design.v
   bugpoint -script <failure.ys>
   write_verilog min.v

- `write_rtlil` is more reliable since `bugpoint` will have run that exact
  code through the failing script; other ``write_*`` commands convert from the
  RTLIL and then back again during the ``read_*`` which can result in
  differences which mean the design no longer fails
- check out :ref:`using_yosys/bugpoint:identifying issues` for more on what to
  do next

.. _minimize your script:

Minimizing scripts
------------------

- reminder to back up original code before modifying it
- if you're using command line, convert it to a script
- if you're using one of the :doc:`/using_yosys/synthesis/synth`, replace it
  with its contents

  + can also do this piece-wise with the ``-run`` option
  + e.g. replacing ``synth -top <top> -lut`` with :ref:`replace_synth`
  + the options ``-top <top> -lut`` can be provided to each `synth` step, or
    to just the step(s) where it is relevant, as done here

.. code-block:: yoscrypt
   :caption: example replacement script for `synth` command
   :name: replace_synth

   synth -top <top> -run :coarse
   synth -lut -run coarse:fine
   synth -lut -run fine:check
   synth -run check:

- remove everything *after* the error occurs
- can use `log` command to print messages to help locate the failure point
- `echo` can also help (``echo on``)

  + if you used a ``-run`` option like in :ref:`replace_synth` above, you can
    now replace the failing step with its contents and repeat the above if
    needed
  + checking the log should tell you the last command that ran which can make
    this easier
  + say we ran :ref:`replace_synth` and were able to remove the ``synth -run
    check:`` and still got our error, then we check the log and we see the last
    thing before the error was ``7.2. Executing MEMORY_MAP pass (converting
    memories to logic and flip-flops).``
  + we can then update our script to the following:

.. code-block:: yoscrypt
   :caption: example replacement script for `synth` when `memory_map` is failing

   synth -top <top> -run :fine
   opt -fast -full
   memory_map


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

- if there are no existing or related issues already, the check out the steps
  for :ref:`using_yosys/bugpoint:creating an issue on github`


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
