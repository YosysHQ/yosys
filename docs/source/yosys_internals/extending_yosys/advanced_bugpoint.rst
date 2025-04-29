Identifying the root cause of bugs
==================================

This document references Yosys internals and is intended for people interested
in solving or investigating Yosys bugs.  This also applies if you are using a
fuzzing tool; fuzzers have a tendency to find many variations of the same bug,
so identifying the root cause is important for avoiding issue spam.

- if the failing command was part of a larger script, such as one of the
  :doc:`/using_yosys/synthesis/synth`, you could try to follow the design
  through the script

  + sometimes when a command is raising an error, you're seeing a symptom rather
    than the underlying issue
  + an earlier command may be putting the design in an invalid state which isn't
    picked up until the error is raised
  + check out :ref:`yosys_internals/extending_yosys/advanced_bugpoint:why context matters`

- if you're familiar with C/C++ you might try to have a look at the source
  code of the command that's failing

  + even if you can't fix the problem yourself, it can be very helpful for
    anyone else investigating if you're able to identify where exactly the
    issue is

Minimizing scripts
------------------

.. TODO:: disclaimer this is intended as advanced usage, and generally not necessary for bug reports

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
   Check out :ref:`yosys_internals/extending_yosys/advanced_bugpoint:Why
   context matters` to learn more.

When a problem is occurring many steps into a script, minimizing the design at
the start of the script isn't always enough to identify the cause of the issue.
Each extra step of the script can lead to larger sections of the input design
being needed for the specific problem to be preserved until it causes a crash.
So to find the smallest possible reproducer it can sometimes be helpful to
remove commands prior to the failure point.

The simplest way to do this is by writing out the design, resetting the current
state, and reading back the design:

.. code-block:: yoscrypt

   write_rtlil <design.il>; design -reset; read_rtlil <design.il>;

In most cases, this can be inserted immediately before the failing command while
still producing the error, allowing you to :ref:`minimize your
RTLIL<using_yosys/bugpoint:minimizing rtlil designs with bugpoint>` with the
``<design.il>`` output.  For our previous example with `memory_map`, if
:ref:`map_reset` still gives the same error, then we should now be able to call
``yosys design.il -p 'memory_map'`` to reproduce it.

.. code-block:: yoscrypt
   :caption: resetting the design immediately before failure
   :name: map_reset

   synth -top <top> -run :fine
   opt -fast -full
   write_rtlil design.il; design -reset; read_rtlil design.il;
   memory_map

If that doesn't give the error (or doesn't give the same error), then you should
try to move the write/reset/read earlier in the script until it does.  If you
have no idea where exactly you should put the reset, the best way is to use a
"binary search" type approach, reducing the possible options by half after each
attempt.

.. note::

   By default, `write_rtlil` doesn't include platform specific IP blocks and
   other primitive cell models which are typically loaded with a ``read_verilog
   -lib`` command at the start of the synthesis script.  You may have to
   duplicate these commands *after* the call to ``design -reset``.  It is also
   possible to write out *everything* with ``select =*; write_rtlil -selected
   <design.il>``.

As an example, your script has 16 commands in it before failing on the 17th. If
resetting immediately before the 17th doesn't reproduce the error, try between
the 8th and 9th (8 is half of the total 16).  If that produces the error then
you can remove everything before the `read_rtlil` and try reset again in the
middle of what's left, making sure to use a different name for the output file
so that you don't overwrite what you've already got.  If the error isn't
produced then you need to go earlier still, so in this case you would do between
the 4th and 5th (4 is half of the previous 8).  Repeat this until you can't
reduce the remaining commands any further.

A more conservative, but more involved, method is to remove or comment out
commands prior to the failing command.  Each command, or group of commands, can
be disabled one at a time while checking if the error still occurs, eventually
giving the smallest subset of commands needed to take the original input through
to the error.  The difficulty with this method is that depending on your design,
some commands may be necessary even if they aren't needed to reproduce the
error.  For example, if your design includes ``process`` blocks, many commands
will fail unless you run the `proc` command.  While this approach can do a
better job of maintaining context, it is often easier to *recover* the context
after the design has been minimized for producing the error.  For more on
recovering context, checkout
:ref:`yosys_internals/extending_yosys/advanced_bugpoint:Why context matters`.


Why context matters
-------------------

- if you did minimized your script, and removed commands prior to the failure
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
