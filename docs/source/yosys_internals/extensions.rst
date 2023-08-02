.. _chapter:prog:

Writing extensions
==================

.. TODO: copypaste

This chapter contains some bits and pieces of information about programming
yosys extensions. Don't be afraid to ask questions on the YosysHQ Slack.

Guidelines
----------

The guidelines directory contains notes on various aspects of Yosys development.
The files GettingStarted and CodingStyle may be of particular interest, and are
reproduced here.

.. literalinclude:: ../temp/GettingStarted
    :language: none
    :caption: guidelines/GettingStarted

.. literalinclude:: ../temp/CodingStyle
    :language: none
    :caption: guidelines/CodingStyle

The "stubsnets" example module
------------------------------

The following is the complete code of the "stubsnets" example module. It is
included in the Yosys source distribution as
``docs/source/CHAPTER_Prog/stubnets.cc``.

.. literalinclude:: ../CHAPTER_Prog/stubnets.cc
    :language: c++
    :linenos:
    :caption: docs/source/CHAPTER_Prog/stubnets.cc

.. literalinclude:: ../CHAPTER_Prog/Makefile
    :language: makefile
    :linenos:
    :caption: docs/source/CHAPTER_Prog/Makefile

.. literalinclude:: ../CHAPTER_Prog/test.v
    :language: verilog
    :linenos:
    :caption: docs/source/CHAPTER_Prog/test.v

Quick guide
-----------

See also: ``docs/resources/PRESENTATION_Prog/*``.

Program components and data formats
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

See :doc:`/yosys_internals/formats/rtlil_rep` document for more information
about the internal data storage format used in Yosys and the classes that it
provides.

This document will focus on the much simpler version of RTLIL left after the
commands ``proc`` and ``memory`` (or ``memory -nomap``):

.. figure:: ../../images/simplified_rtlil.*
    :class: width-helper
    :name: fig:Simplified_RTLIL

    Simplified RTLIL entity-relationship diagram without memories and processes

It is possible to only work on this simpler version:

.. code:: c++

    for (RTLIL::Module *module : design->selected_modules() {
        if (module->has_memories_warn() || module->has_processes_warn())
            continue;
        ....
    }

When trying to understand what a command does, creating a small test case to
look at the output of ``dump`` and ``show`` before and after the command has
been executed can be helpful.  The :doc:`/using_yosys/more_scripting/selections`
document has more information on using these commands.

.. TODO: copypaste

Creating modules from scratch
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Let's create the following module using the RTLIL API:

.. code:: Verilog

    module absval(input signed [3:0] a, output [3:0] y);
        assign y = a[3] ? -a : a;
    endmodule

.. code:: C++

    RTLIL::Module *module = new RTLIL::Module;
    module->name = "\\absval";

    RTLIL::Wire *a = module->addWire("\\a", 4);
    a->port_input = true;
    a->port_id = 1;

    RTLIL::Wire *y = module->addWire("\\y", 4);
    y->port_output = true;
    y->port_id = 2;

    RTLIL::Wire *a_inv = module->addWire(NEW_ID, 4);
    module->addNeg(NEW_ID, a, a_inv, true);
    module->addMux(NEW_ID, a, a_inv, RTLIL::SigSpec(a, 1, 3), y);

    module->fixup_ports();

Modifying modules
~~~~~~~~~~~~~~~~~

Most commands modify existing modules, not create new ones.

When modifying existing modules, stick to the following DOs and DON'Ts:

- Do not remove wires. Simply disconnect them and let a successive ``clean``
  command worry about removing it.
- Use ``module->fixup_ports()`` after changing the ``port_*`` properties of
  wires.
- You can safely remove cells or change the ``connections`` property of a cell,
  but be careful when changing the size of the ``SigSpec`` connected to a cell
  port.

- Use the ``SigMap`` helper class (see next slide) when you need a unique handle for each signal bit.

Using the SigMap helper class
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Consider the following module:

.. code:: Verilog

    module test(input a, output x, y);
        assign x = a, y = a;
    endmodule

In this case ``a``, ``x``, and ``y`` are all different names for the same signal. However:

.. code:: C++

    RTLIL::SigSpec a(module->wire("\\a")), x(module->wire("\\x")),
                                           y(module->wire("\\y"));
    log("%d %d %d\n", a == x, x == y, y == a); // will print "0 0 0"

The ``SigMap`` helper class can be used to map all such aliasing signals to a
unique signal from the group (usually the wire that is directly driven by a cell or port).

.. code:: C++

    SigMap sigmap(module);
    log("%d %d %d\n", sigmap(a) == sigmap(x), sigmap(x) == sigmap(y),
                      sigmap(y) == sigmap(a)); // will print "1 1 1"

Printing log messages
~~~~~~~~~~~~~~~~~~~~~

The ``log()`` function is a ``printf()``-like function that can be used to create log messages.

Use ``log_signal()`` to create a C-string for a SigSpec object:

.. code:: C++

    log("Mapped signal x: %s\n", log_signal(sigmap(x)));

The pointer returned by ``log_signal()`` is automatically freed by the log
framework at a later time.

Use ``log_id()`` to create a C-string for an ``RTLIL::IdString``:

.. code:: C++

    log("Name of this module: %s\n", log_id(module->name));

Use ``log_header()`` and ``log_push()``/``log_pop()`` to structure log messages:

.. code:: C++

    log_header(design, "Doing important stuff!\n");
    log_push();
    for (int i = 0; i < 10; i++)
        log("Log message #%d.\n", i);
    log_pop();

Error handling
~~~~~~~~~~~~~~

Use ``log_error()`` to report a non-recoverable error:

.. code:: C++

    if (design->modules.count(module->name) != 0)
        log_error("A module with the name %s already exists!\n",
                   RTLIL::id2cstr(module->name));

Use ``log_cmd_error()`` to report a recoverable error:

.. code:: C++

    if (design->selection_stack.back().empty())
        log_cmd_error("This command can't operator on an empty selection!\n");

Use ``log_assert()`` and ``log_abort()`` instead of ``assert()`` and ``abort()``.

Creating a command
~~~~~~~~~~~~~~~~~~

Simply create a global instance of a class derived from ``Pass`` to create
a new yosys command:

.. code:: C++

    #include "kernel/yosys.h"
    USING_YOSYS_NAMESPACE

    struct MyPass : public Pass {
        MyPass() : Pass("my_cmd", "just a simple test") { }
        virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
        {
            log("Arguments to my_cmd:\n");
            for (auto &arg : args)
            log("  %s\n", arg.c_str());

            log("Modules in current design:\n");
            for (auto mod : design->modules())
            log("  %s (%d wires, %d cells)\n", log_id(mod),
                GetSize(mod->wires()), GetSize(mod->cells()));
        }
    } MyPass;

Creating a plugin
~~~~~~~~~~~~~~~~~

Yosys can be extended by adding additional C++ code to the Yosys code base, or
by loading plugins into Yosys.

Use the following command to compile a Yosys plugin:

.. code::

    yosys-config --exec --cxx --cxxflags --ldflags \
             -o my_cmd.so -shared my_cmd.cc --ldlibs

Or shorter:

.. code::

    yosys-config --build my_cmd.so my_cmd.cc

Load the plugin using the yosys ``-m`` option:

.. code::

    yosys -m ./my_cmd.so -p 'my_cmd foo bar'
