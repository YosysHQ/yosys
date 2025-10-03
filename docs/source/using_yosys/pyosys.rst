Scripting with Pyosys
=====================

Pyosys is a limited subset of the Yosys C++ API (aka "libyosys") made available
using the Python programming language.

Like ``.ys`` and ``.tcl`` scripts, Pyosys provides an interface to write Yosys
scripts in the Python programming language, giving you the benefits of
a type system, control flow, object-oriented programming, and more; especially
that the other options lack a type system and control flow/OOP in Tcl is
limited.

Though unlike these two, Pyosys goes a bit further, allowing you to use the
Yosys API to implement advanced functionality that would otherwise require
custom passes written in C++.


Getting Pyosys
--------------

Pyosys supports CPython 3.8 or higher. You can access Pyosys using one of two
methods:

1. Compiling Yosys with the Makefile flag ``ENABLE_PYOSYS=1``

   This adds the flag ``-y`` to the Yosys binary, which allows you to execute
   Python scripts using an interpreter embedded in Yosys itself:

   ``yosys -y ./my_pyosys_script.py``

2. Installing the Pyosys wheels

   On macOS and GNU/Linux you can install pre-built wheels of Yosys using
   ``pip``:

   ``python3 -m pip install pyosys``

   Which then allows you to run your scripts as follows:

   ``python3 ./my_pyosys_script.py``


Scripting and Database Inspection
---------------------------------

To start with, you have to import libyosys as follows:

.. code-block:: python

   from pyosys import libyosys


As a reminder, Python allows you to alias imported modules and objects, so
this import may be preferable for terseness:

.. code-block:: python

   from pyosys import libyosys as ys


Now, scripting is actually quite similar to ``.ys`` and ``.tcl`` script in that
you can provide mostly text commands. Albeit, you can construct your scripts
to use Python's amenities like conditional execution, loops, and functions:

.. code-block:: python

   do_flatten = True

   ys.run_pass("read_verilog tests/simple/fiedler-cooley.v")
   ys.run_pass("hierarchy -check -auto-top")
   if do_flatten:
      ys.run_pass("flatten")

…but this does not strictly provide anything that Tcl scripts do not provide you
with. The real power of using Pyosys comes from the fact you can manually
instantiate, manage, and interact with the design database.

As an example, here is the same script with a manually instantiated design.

.. literalinclude:: /code_examples/pyosys/simple_database.py
   :start-after: loading design
   :end-before: top module inspection
   :language: python

What's new here is that you can manually inspect the design's database. This
gives you access to a huge chunk of the design database API as declared in
the ``kernel/rtlil.h`` header.

For example, here's how to list the input and output ports of the top module
of your design:

.. literalinclude:: /code_examples/pyosys/simple_database.py
   :start-after: top module inspection
   :end-before: # synth
   :language: python

.. tip::

   C++ data structures in Yosys are bridged to Python such that they have a
   pretty similar API to Python objects, for example:

   - ``std::vector`` supports the same methods as
     `iterables <https://docs.python.org/3/glossary.html#term-iterable>`_ in
     Python.
   - ``std::set`` and hashlib ``pool`` support the same methods as ``set``\s in
     Python. While ``set`` is ordered, ``pool`` is not and modifications may
     cause a complete reordering of the set.
   - ``dict`` supports the same methods as ``dict``\s in Python, albeit it is
     unordered, and modifications may cause a complete reordering of the
     dictionary.
   - ``idict`` uses a custom set of methods because it doesn't map very cleanly
     to an existing Python data structure. See ``pyosys/hashlib.h`` for more
     info.

   For most operations, the Python equivalents are also supported as arguments
   where they will automatically be cast to the right type, so you do not have
   to manually instantiate the right underlying C++ object(s) yourself.

Modifying the Database
----------------------

.. warning::

   Any modifications to the database may invalidate previous references held
   by Python, just as if you were writing C++. Pyosys does not currently attempt
   to keep deleted objects alive if a reference is held by Python.

You are not restricted to inspecting the database either: you have the ability
to modify it, and introduce new elements and/or changes to your design.

As a demonstrative example, let's assume we want to add an enable line to all
flip-flops in our fiedler-cooley design.

First of all, we will run :yoscrypt:`synth` to convert all of the logic to
Yosys's internal cell structure (see :ref:`sec:celllib_gates`):

.. literalinclude:: /code_examples/pyosys/simple_database.py
   :start-after: # synth
   :end-before: adding the enable line
   :language: python

Next, we need to add the new port. The method for this is ``Module::addWire``\.

.. tip::

   IdString is Yosys's internal representation of strings used as identifiers
   within Verilog designs. They are efficient as only integers are stored and
   passed around, but they can be translated to and from normal strings at will.

   Pyosys will automatically cast Python strings to IdStrings for you, but the
   rules around IdStrings apply, namely that *broadly*:

   - Identifiers for internal cells must start with ``$``\.
   - All other identifiers must start with ``\``\.

.. literalinclude:: /code_examples/pyosys/simple_database.py
   :start-after: adding the enable line
   :end-before: hooking the enable line
   :language: python

Notice how we modified the wire then called a method to make Yosys re-process
the ports.

Next, we can iterate over all constituent cells, and if they are of the type
``$_DFF_P_``, we do two things:

1. Change their type to ``$_DFFE_PP_`` to enable hooking up an enable signal.
2. Hooking up the enable signal.

.. literalinclude:: /code_examples/pyosys/simple_database.py
   :start-after: hooking the enable line
   :end-before: run check
   :language: python

To verify that you did everything correctly, it is prudent to call ``.check()``
on the module you're manipulating as follows after you're done with a set of
changes:

.. literalinclude:: /code_examples/pyosys/simple_database.py
   :start-after: run check
   :end-before: write output
   :language: python

And then finally, write your outputs. Here, I choose an intermediate Verilog
file and :yoscrypt:`synth_ice40` to map it to the iCE40 architecture.

.. literalinclude:: /code_examples/pyosys/simple_database.py
   :start-after: write output
   :language: python

And voilà, you will note that in the intermediate output, all ``always @``
statements should have an ``if (enable)``\.

Encapsulating as Passes
-----------------------

Just like when writing C++, you can encapsulate routines in terms of "passes",
which adds your Pass to a global registry of commands accessible using
``run_pass``\.

.. literalinclude:: /code_examples/pyosys/pass.py
   :language: python

In general, abstract classes and virtual methods are not really supported by
Pyosys due to their complexity, but there are two exceptions which are:

- ``Pass`` in ``kernel/register.h``
- ``Monitor`` in ``kernel/rtlil.h``
