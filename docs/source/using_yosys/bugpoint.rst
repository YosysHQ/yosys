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

- are there any warnings before the error (either immediately before or in an
  earlier command) that could be related?
- does calling `check` before the failure give any errors or warnings?
- did you call `hierarchy` before the failure?

  + can you call ``hierarchy -check``?

- make sure to back up your code (design source and yosys script(s)) before
  making any modifications

  + even if the code itself isn't important, this can help avoid "losing" the
    error while trying to debug it


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
leak or excessive runtime.  Note however that unlike the `exec` command, there
is currently no way to check the return status or messages from the wrapper
process; only a binary pass/fail.

.. TODO:: above note pending updated bugpoint #5068


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

.. TODO::  above note pending updated bugpoint #5068

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

.. TODO:: note on ``!`` (link to :ref:`getting_started/scripting_intro:script parsing`)

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

- manual process
- made easier if the error message is able to identify the source line or name
  of the object
- reminder to back up original code before modifying it
- if a specific module is causing the problem, try to set that as the top
  module, you can then remove 

  + if the problem is parameter specific you may be able to change the default
    parameters so that they match the problematic configuration

- if you have no idea what is or is not relevant, try to follow a "binary
  search" type approach where you remove (or comment out) roughly half of what's
  left at a time
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

.. warning::

   If you are using a fuzzer to find bugs, follow the instructions for
   :doc:`/yosys_internals/extending_yosys/advanced_bugpoint`.  **Do not** open
   more than one fuzzer generated issue at a time if you can not identify the
   root cause.  If you are found to be doing this, your issues may be closed
   without further investigation.

- search `the existing issues`_ and see if someone has already made a bug report

  + this is where changing the design and finding the limits of what causes the
    failure really comes in handy
  + if you're more familiar with how the problem can arise, you may be able to
    find a related issue more easily
  + if an issue already exists for one case of the problem but you've found
    other cases, you can comment on the issue and help get it solved

.. _the existing issues: https://github.com/YosysHQ/yosys/issues

- if there are no existing or related issues already, then check out the steps
  for :ref:`yosys_internals/extending_yosys/contributing:reporting bugs`
