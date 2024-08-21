Writing extensions
==================

.. role:: yoscrypt(code)
   :language: yoscrypt

.. todo:: check text is coherent

.. todo:: update to use :file:`/code_examples/extensions/test*.log`

This chapter contains some bits and pieces of information about programming
yosys extensions. Don't be afraid to ask questions on the YosysHQ Slack.

The `guidelines/` directory of the Yosys source code contains notes on various
aspects of Yosys development. In particular, the files GettingStarted and
CodingStyle may be of interest.

.. todo:: what's in guidelines/GettingStarted that's missing from the manual?

Quick guide
-----------

Code examples from this section are included in the
|code_examples/extensions|_ directory of the Yosys source code.

.. |code_examples/extensions| replace:: :file:`docs/source/code_examples/extensions`
.. _code_examples/extensions: https://github.com/YosysHQ/yosys/tree/main/docs/source/code_examples/extensions


Program components and data formats
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

See :doc:`/yosys_internals/formats/rtlil_rep` document for more information
about the internal data storage format used in Yosys and the classes that it
provides.

This document will focus on the much simpler version of RTLIL left after the
commands :cmd:ref:`proc` and :cmd:ref:`memory` (or :yoscrypt:`memory -nomap`):

.. figure:: /_images/internals/simplified_rtlil.*
    :class: width-helper invert-helper
    :name: fig:Simplified_RTLIL

    Simplified RTLIL entity-relationship diagram without memories and processes

It is possible to only work on this simpler version:

.. todo:: consider replacing inline code

.. code:: c++

    for (RTLIL::Module *module : design->selected_modules() {
        if (module->has_memories_warn() || module->has_processes_warn())
            continue;
        ....
    }

When trying to understand what a command does, creating a small test case to
look at the output of :cmd:ref:`dump` and :cmd:ref:`show` before and after the
command has been executed can be helpful.
:doc:`/using_yosys/more_scripting/selections` has more information on using
these commands.

Creating a command
~~~~~~~~~~~~~~~~~~

.. todo:: add/expand supporting text

Let's create a very simple test command which prints the arguments we called it
with, and lists off the current design's modules.

.. literalinclude:: /code_examples/extensions/my_cmd.cc
   :language: c++
   :lines: 1, 4, 6, 7-20
   :caption: Example command :yoscrypt:`my_cmd` from :file:`my_cmd.cc`
   
Note that we are making a global instance of a class derived from
``Yosys::Pass``, which we get by including :file:`kernel/yosys.h`.

Compiling to a plugin
~~~~~~~~~~~~~~~~~~~~~

Yosys can be extended by adding additional C++ code to the Yosys code base, or
by loading plugins into Yosys.  For maintainability it is generally recommended
to create plugins.

The following command compiles our example :yoscrypt:`my_cmd` to a Yosys plugin:

.. todo:: replace inline code

.. code:: shell

   yosys-config --exec --cxx --cxxflags --ldflags \
   -o my_cmd.so -shared my_cmd.cc --ldlibs

Or shorter:

.. code:: shell

   yosys-config --build my_cmd.so my_cmd.cc

Running Yosys with the ``-m`` option allows the plugin to be used.  Here's a
quick example that also uses the ``-p`` option to run :yoscrypt:`my_cmd foo
bar`.

.. code:: shell-session

   $ yosys -m ./my_cmd.so -p 'my_cmd foo bar'

   -- Running command `my_cmd foo bar' --
   Arguments to my_cmd:
     my_cmd
     foo
     bar
   Modules in current design:

Creating modules from scratch
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Let's create the following module using the RTLIL API:

.. literalinclude:: /code_examples/extensions/absval_ref.v
   :language: Verilog
   :caption: absval_ref.v

We'll do the same as before and format it as a a ``Yosys::Pass``.

.. literalinclude:: /code_examples/extensions/my_cmd.cc
   :language: c++
   :lines: 23-47
   :caption: :yoscrypt:`test1` - creating the absval module, from :file:`my_cmd.cc`

.. code:: shell-session

   $ yosys -m ./my_cmd.so -p 'test1' -Q

   -- Running command `test1' --
   Name of this module: absval

And if we look at the schematic for this new module we see the following:

.. figure:: /_images/code_examples/extensions/test1.*
   :class: width-helper invert-helper

   Output of ``yosys -m ./my_cmd.so -p 'test1; show'``

Modifying modules
~~~~~~~~~~~~~~~~~

Most commands modify existing modules, not create new ones.

When modifying existing modules, stick to the following DOs and DON'Ts:

- Do not remove wires. Simply disconnect them and let a successive
  :cmd:ref:`clean` command worry about removing it.
- Use ``module->fixup_ports()`` after changing the ``port_*`` properties of
  wires.
- You can safely remove cells or change the ``connections`` property of a cell,
  but be careful when changing the size of the ``SigSpec`` connected to a cell
  port.
- Use the ``SigMap`` helper class (see next section) when you need a unique
  handle for each signal bit.

Using the SigMap helper class
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Consider the following module:

.. literalinclude:: /code_examples/extensions/sigmap_test.v
   :language: Verilog
   :caption: :file:`sigmap_test.v`

In this case ``a``, ``x``, and ``y`` are all different names for the same
signal. However:

.. todo:: use my_cmd.cc literalincludes

.. code:: C++

    RTLIL::SigSpec a(module->wire("\\a")), x(module->wire("\\x")),
                                           y(module->wire("\\y"));
    log("%d %d %d\n", a == x, x == y, y == a); // will print "0 0 0"

The ``SigMap`` helper class can be used to map all such aliasing signals to a
unique signal from the group (usually the wire that is directly driven by a cell
or port).

.. code:: C++

    SigMap sigmap(module);
    log("%d %d %d\n", sigmap(a) == sigmap(x), sigmap(x) == sigmap(y),
                      sigmap(y) == sigmap(a)); // will print "1 1 1"

Printing log messages
~~~~~~~~~~~~~~~~~~~~~

The ``log()`` function is a ``printf()``-like function that can be used to
create log messages.

Use ``log_signal()`` to create a C-string for a SigSpec object:

.. code:: C++

    log("Mapped signal x: %s\n", log_signal(sigmap(x)));

The pointer returned by ``log_signal()`` is automatically freed by the log
framework at a later time.

Use ``log_id()`` to create a C-string for an ``RTLIL::IdString``:

.. code:: C++

    log("Name of this module: %s\n", log_id(module->name));

Use ``log_header()`` and ``log_push()``/\ ``log_pop()`` to structure log
messages:

.. todo:: replace inline code

.. code:: C++

    log_header(design, "Doing important stuff!\n");
    log_push();
    for (int i = 0; i < 10; i++)
        log("Log message #%d.\n", i);
    log_pop();

Error handling
~~~~~~~~~~~~~~

Use ``log_error()`` to report a non-recoverable error:

.. todo:: replace inline code

.. code:: C++

    if (design->modules.count(module->name) != 0)
        log_error("A module with the name %s already exists!\n",
                   RTLIL::id2cstr(module->name));

Use ``log_cmd_error()`` to report a recoverable error:

.. code:: C++

    if (design->selection_stack.back().empty())
        log_cmd_error("This command can't operator on an empty selection!\n");

Use ``log_assert()`` and ``log_abort()`` instead of ``assert()`` and ``abort()``.

The "stubnets" example module
------------------------------

The following is the complete code of the "stubnets" example module. It is
included in the Yosys source distribution under |code_examples/stubnets|_.

.. |code_examples/stubnets| replace:: :file:`docs/source/code_examples/stubnets`
.. _code_examples/stubnets: https://github.com/YosysHQ/yosys/tree/main/docs/source/code_examples/stubnets

.. literalinclude:: /code_examples/stubnets/stubnets.cc
    :language: c++
    :linenos:
    :caption: :file:`stubnets.cc`

.. literalinclude:: /code_examples/stubnets/Makefile
    :language: makefile
    :linenos:
    :caption: :file:`Makefile`

.. literalinclude:: /code_examples/stubnets/test.v
    :language: verilog
    :linenos:
    :caption: :file:`test.v`
