Writing a new backend using FunctionalIR
========================================

What is FunctionalIR
--------------------

To simplify the writing of backends for functional languages or similar targets,
Yosys provides an alternative intermediate representation called FunctionalIR
which maps more directly on those targets.

FunctionalIR represents the design as a function ``(inputs, current_state) ->
(outputs, next_state)``. This function is broken down into a series of
assignments to variables. Each assignment is a simple operation, such as an
addition. Complex operations are broken up into multiple steps. For example, an
RTLIL addition will be translated into a sign/zero extension of the inputs,
followed by an addition.

Like SSA form, each variable is assigned to exactly once. We can thus treat
variables and assignments as equivalent and, since this is a graph-like
representation, those variables are also called "nodes". Unlike RTLIL's cells
and wires representation, this representation is strictly ordered (topologically
sorted) with definitions preceding their use.

Every node has a "sort" (the FunctionalIR term for what might otherwise be
called a "type"). The sorts available are

- ``bit[n]`` for an ``n``-bit bitvector, and
- ``memory[n,m]`` for an immutable array of ``2**n`` values of sort ``bit[m]``.

In terms of actual code, Yosys provides a class ``Functional::IR`` that
represents a design in FunctionalIR. ``Functional::IR::from_module`` generates
an instance from an RTLIL module. The entire design is stored as a whole in an
internal data structure. To access the design, the ``Functional::Node`` class
provides a reference to a particular node in the design. The ``Functional::IR``
class supports the syntax ``for(auto node : ir)`` to iterate over every node.

``Functional::IR`` also keeps track of inputs, outputs and states. By a "state"
we mean a pair of a "current state" input and a "next state" output. One such
pair is created for every register and for every memory. Every input, output and
state has a name (equal to their name in RTLIL), a sort and a kind. The kind
field usually remains as the default value ``$input``, ``$output`` or
``$state``, however some RTLIL cells such as ``$assert`` or ``$anyseq`` generate
auxiliary inputs/outputs/states that are given a different kind to distinguish
them from ordinary RTLIL inputs/outputs/states.

- To access an individual input/output/state, use ``ir.input(name, kind)``,
  ``ir.output(name, kind)`` or ``ir.state(name, kind)``. ``kind`` defaults to
  the default kind.
- To iterate over all inputs/outputs/states of a certain kind, methods
  ``ir.inputs``, ``ir.outputs``, ``ir.states`` are provided. Their argument
  defaults to the default kinds mentioned.
- To iterate over inputs/outputs/states of any kind, use ``ir.all_inputs``,
  ``ir.all_outputs`` and ``ir.all_states``.
- Outputs have a node that indicate the value of the output, this can be
  retrieved via ``output.value()``.
- States have a node that indicate the next value of the state, this can be
  retrieved via ``state.next_value()``. They also have an initial value that is
  accessed as either ``state.initial_value_signal()`` or
  ``state.initial_value_memory()``, depending on their sort.

Each node has a "function", which defines its operation (for a complete list of
functions and a specification of their operation, see ``functional.h``).
Functions are represented as an enum ``Functional::Fn`` and the function field
can be accessed as ``node.fn()``. Since the most common operation is a switch
over the function that also accesses the arguments, the ``Node`` class provides
a method ``visit`` that implements the visitor pattern. For example, for an
addition node ``node`` with arguments ``n1`` and ``n2``, ``node.visit(visitor)``
would call ``visitor.add(node, n1, n2)``. Thus typically one would implement a
class with a method for every function. Visitors should inherit from either
``Functional::AbstractVisitor<ReturnType>`` or
``Functional::DefaultVisitor<ReturnType>``. The former will produce a compiler
error if a case is unhandled, the latter will call ``default_handler(node)``
instead. Visitor methods should be marked as ``override`` to provide compiler
errors if the arguments are wrong.

Utility classes
~~~~~~~~~~~~~~~

``functional.h`` also provides utility classes that are independent of the main
FunctionalIR representation but are likely to be useful for backends.

``Functional::Writer`` provides a simple formatting class that wraps a
``std::ostream`` and provides the following methods:

- ``writer << value`` wraps ``os << value``.
- ``writer.print(fmt, value0, value1, value2, ...)`` replaces ``{0}``, ``{1}``,
  ``{2}``, etc in the string ``fmt`` with ``value0``, ``value1``, ``value2``,
  resp. Each value is formatted using ``os << value``. It is also possible to
  write ``{}`` to refer to one past the last index, i.e. ``{1} {} {} {7} {}`` is
  equivalent to ``{1} {2} {3} {7} {8}``.
- ``writer.print_with(fn, fmt, value0, value1, value2, ...)`` functions much the
  same as ``print`` but it uses ``os << fn(value)`` to print each value and
  falls back to ``os << value`` if ``fn(value)`` is not legal.

``Functional::Scope`` keeps track of variable names in a target language. It is
used to translate between different sets of legal characters and to avoid
accidentally re-defining identifiers. Users should derive a class from ``Scope``
and supply the following:

- ``Scope<Id>`` takes a template argument that specifies a type that's used to
  uniquely distinguish variables. Typically this would be ``int`` (if variables
  are used for ``Functional::IR`` nodes) or ``IdString``.
- The derived class should provide a constructor that calls ``reserve`` for
  every reserved word in the target language.
- A method ``bool is_character_legal(char c, int index)`` has to be provided
  that returns ``true`` iff ``c`` is legal in an identifier at position
  ``index``.

Given an instance ``scope`` of the derived class, the following methods are then
available:

- ``scope.reserve(std::string name)`` marks the given name as being in-use
- ``scope.unique_name(IdString suggestion)`` generates a previously unused name
  and attempts to make it similar to ``suggestion``.
- ``scope(Id id, IdString suggestion)`` functions similar to ``unique_name``,
  except that multiple calls with the same ``id`` are guaranteed to retrieve the
  same name (independent of ``suggestion``).

``sexpr.h`` provides classes that represent and pretty-print s-expressions.
S-expressions can be constructed with ``SExpr::list``, for example ``SExpr expr
= SExpr::list("add", "x", SExpr::list("mul", "y", "z"))`` represents ``(add x
(mul y z))`` (by adding ``using SExprUtil::list`` to the top of the file,
``list`` can be used as shorthand for ``SExpr::list``). For prettyprinting,
``SExprWriter`` wraps an ``std::ostream`` and provides the following methods:

- ``writer << sexpr`` writes the provided expression to the output, breaking
  long lines and adding appropriate indentation.
- ``writer.open(sexpr)`` is similar to ``writer << sexpr`` but will omit the
  last closing parenthesis. Further arguments can then be added separately with
  ``<<`` or ``open``. This allows for printing large s-expressions without
  needing to construct the whole expression in memory first.
- ``writer.open(sexpr, false)`` is similar to ``writer.open(sexpr)`` but further
  arguments will not be indented. This is used to avoid unlimited indentation on
  structures with unlimited nesting.
- ``writer.close(n = 1)`` closes the last ``n`` open s-expressions.
- ``writer.push()`` and ``writer.pop()`` are used to automatically close
  s-expressions. ``writer.pop()`` closes all s-expressions opened since the last
  call to ``writer.push()``.
- ``writer.comment(string)`` writes a comment on a separate-line.
  ``writer.comment(string, true)`` appends a comment to the last printed
  s-expression.
- ``writer.flush()`` flushes any buffering and should be called before any
  direct access to the underlying ``std::ostream``. It does not close unclosed
  parentheses.
- The destructor calls ``flush`` but also closes all unclosed parentheses.

.. _minimal backend:

Example: A minimal functional backend
-------------------------------------

At its most basic, there are three steps we need to accomplish for a minimal
functional backend.  First, we need to convert our design into FunctionalIR.
This is most easily done by calling the ``Functional::IR::from_module()`` static
method with our top-level module, or iterating over and converting each of the
modules in our design.  Second, we need to handle each of the
``Functional::Node``\ s in our design.  Iterating over the ``Functional::IR``
includes reading the module inputs and current state, but not writing the
results.  So our final step is to handle the outputs and next state.

In order to add an output command to Yosys, we implement the ``Yosys::Backend``
class and provide an instance of it:

.. literalinclude:: /code_examples/functional/dummy.cc
   :language: c++
   :caption: Example source code for a minimal functional backend, ``dummy.cc``

Because we are using the ``Backend`` class, our ``"functional_dummy"`` is
registered as the ``write_functional_dummy`` command.  The ``execute`` method is
the part that runs when the user calls the command, handling any options,
preparing the output file for writing, and iterating over selected modules in
the design.  Since we don't have any options here, we set ``argidx = 1`` and
call the ``extra_args()`` method.  This method will read the command arguments,
raising an error if there are any unexpected ones.  It will also assign the
pointer ``f`` to the output file, or stdout if none is given.

.. note::

   For more on adding new commands to Yosys and how they work, refer to
   :doc:`/yosys_internals/extending_yosys/extensions`.

For this minimal example all we are doing is printing out each node.  The
``node.name()`` method returns an ``RTLIL::IdString``, which we convert for
printing with ``id2cstr()``.  Then, to print the function of the node, we use
``node.to_string()`` which gives us a string of the form ``function(args)``. The
``function`` part is the result of ``Functional::IR::fn_to_string(node.fn())``;
while ``args`` is the zero or more arguments passed to the function, most
commonly the name of another node.  Behind the scenes, the ``node.to_string()``
method actually wraps ``node.visit(visitor)`` with a private visitor whose
return type is ``std::string``.

Finally we iterate over the module's outputs and states, using
``Functional::IROutput::value()`` and ``Functional::IRState::next_value()``
respectively in order to get the results of the transfer function.

Example: Adapting SMT-LIB backend for Rosette
---------------------------------------------

This section will introduce the SMT-LIB functional backend
(`write_functional_smt2`) and what changes are needed to work with another
s-expression target, `Rosette`_ (`write_functional_rosette`).

.. _Rosette: http://emina.github.io/rosette/

Overview
~~~~~~~~

   Rosette is a solver-aided programming language that extends `Racket`_ with
   language constructs for program synthesis, verification, and more. To verify
   or synthesize code, Rosette compiles it to logical constraints solved with
   off-the-shelf `SMT`_ solvers.

   -- https://emina.github.io/rosette/

.. _Racket: http://racket-lang.org/
.. _SMT: http://smtlib.cs.uiowa.edu/

Rosette, being backed by SMT solvers and written with s-expressions, uses code
very similar to the `write_functional_smt2` output.  As a result, the SMT-LIB
functional backend can be used as a starting point for implementing a Rosette
backend.

Full code listings for the initial SMT-LIB backend and the converted Rosette
backend are included in the Yosys source repository under
:file:`backends/functional` as ``smtlib.cc`` and ``smtlib_rosette.cc``
respectively.  Note that the Rosette language is an extension of the Racket
language; this guide tends to refer to Racket when talking about the underlying
semantics/syntax of the language.

The major changes from the SMT-LIB backend are as follows:

- all of the ``Smt`` prefixes in names are replaced with ``Smtr`` to mean
  ``smtlib_rosette``;
- syntax is adjusted for Racket;
- data structures for input/output/state are changed from using
  ``declare-datatype`` with statically typed fields, to using ``struct`` with no
  static typing;
- the transfer function also loses its static typing;
- sign/zero extension in Rosette use the output width instead of the number of
  extra bits, gaining static typing;
- the single scope is traded for a global scope with local scope for each
  struct;
- initial state is provided as a constant value instead of a set of assertions;
- and the ``-provides`` option is introduced to more easily use generated code
  within Rosette based applications.

Scope
~~~~~

Our first addition to the `minimal backend`_ above is that for both SMT-LIB and
Rosette backends, we are now targetting real languages which bring with them
their own sets of constraints with what we can use as identifiers.  This is
where the ``Functional::Scope`` class described above comes in; by using this
class we can safely rename our identifiers in the generated output without
worrying about collisions or illegal names/characters.

In the SMT-LIB version, the ``SmtScope`` class implements ``Scope<int>``;
provides a constructor that iterates over a list of reserved keywords, calling
``reserve`` on each; and defines the ``is_character_legal`` method to reject any
characters which are not allowed in SMT-LIB variable names to then be replaced
with underscores in the output.  To use this scope we create an instance of it,
and call the ``Scope::unique_name()`` method to generate a unique and legal name
for each of our identifiers.

In the Rosette version we update the list of legal ascii characters in the
``is_character_legal`` method to only those allowed in Racket variable names.

.. literalinclude:: /generated/functional/rosette.diff
   :language: diff
   :caption: diff of ``Scope`` class
   :start-at: -struct SmtScope : public Functional::Scope<int> {
   :end-at: };

For the reserved keywords we trade the SMT-LIB specification for Racket to
prevent parts of our design from accidentally being treated as Racket code. We
also no longer need to reserve ``pair``, ``first``, and ``second``.  In
`write_functional_smt2` these are used for combining the ``(inputs,
current_state)`` and ``(outputs, next_state)`` into a single variable.  Racket
provides this functionality natively with ``cons``, which we will see later.

.. inlined diff for skipping the actual lists
.. code-block:: diff
   :caption: diff of ``reserved_keywords`` list

    const char *reserved_keywords[] = {
   -  // reserved keywords from the smtlib spec
   -  ...
   +  // reserved keywords from the racket spec
   +  ...

      // reserved for our own purposes
   -  "pair", "Pair", "first", "second",
   -  "inputs", "state",
   +  "inputs", "state", "name",
      nullptr
    };

.. note:: We skip over the actual list of reserved keywords from both the smtlib
   and racket specifications to save on space in this document.

Sort
~~~~

Next up in `write_functional_smt2` we see the ``Sort`` class.  This is a wrapper
for the ``Functional::Sort`` class, providing the additional functionality of
mapping variable declarations to s-expressions with the ``to_sexpr()`` method.
The main change from ``SmtSort`` to ``SmtrSort`` is a syntactical one with
signals represented as ``bitvector``\ s, and memories as ``list``\ s of signals.

.. literalinclude:: /generated/functional/rosette.diff
   :language: diff
   :caption: diff of ``Sort`` wrapper
   :start-at: SExpr to_sexpr() const {
   :end-before: };

Struct
~~~~~~

As we saw in the `minimal backend`_ above, the ``Functional::IR`` class tracks
the set of inputs, the set of outputs, and the set of "state" variables.  The
SMT-LIB backend maps each of these sets into its own ``SmtStruct``, with each
variable getting a corresponding field in the struct and a specified `Sort`_.
`write_functional_smt2` then defines each of these structs as a new
``datatype``, with each element being strongly-typed.

In Rosette, rather than defining new datatypes for our structs, we use the
native ``struct``.  We also only declare each field by name because Racket
provides less static typing.  For ease of use, we provide the expected type for
each field as comments.

.. literalinclude:: /generated/functional/rosette.diff
   :language: diff
   :caption: diff of ``write_definition`` method
   :start-at: void write_definition
   :end-before: template<typename Fn> void write_value

Each field is added to the ``SmtStruct`` with the ``insert`` method, which also
reserves a unique name (or accessor) within the `Scope`_.  These accessors
combine the struct name and field name and are globally unique, being used in
the ``access`` method for reading values from the input/current state.

.. literalinclude:: /generated/functional/smtlib.cc
   :language: c++
   :caption: ``Struct::access()`` method
   :start-at: SExpr access(
   :end-before: };

In Rosette, struct fields are accessed as ``<struct_name>-<field_name>`` so
including the struct name in the field name would be redundant.  For
`write_functional_rosette` we instead choose to make field names unique only
within the struct, while accessors are unique across the whole module.  We thus
modify the class constructor and ``insert`` method to support this; providing
one scope that is local to the struct (``local_scope``) and one which is shared
across the whole module (``global_scope``), leaving the ``access`` method
unchanged.

.. literalinclude:: /generated/functional/rosette.diff
   :language: diff
   :caption: diff of struct constructor
   :start-at: SmtStruct(std::string name, SmtScope &scope)
   :end-before: void write_definition

Finally, ``SmtStruct`` also provides a ``write_value`` template method which
calls a provided function on each element in the struct.  This is used later for
assigning values to the output/next state pair.  The only change here is to
remove the check for zero-argument constructors since this is not necessary with
Rosette ``struct``\ s.

.. literalinclude:: /generated/functional/rosette.diff
   :language: diff
   :caption: diff of ``write_value`` method
   :start-at: template<typename Fn> void write_value
   :end-before: SExpr access

PrintVisitor
~~~~~~~~~~~~

Remember in the `minimal backend`_ we converted nodes into strings for writing
using the ``node.to_string()`` method, which wrapped ``node.visit()`` with a
private visitor.  We now want a custom visitor which can convert nodes into
s-expressions.  This is where the ``PrintVisitor`` comes in, implementing the
abstract ``Functional::AbstractVisitor`` class with a return type of ``SExpr``.
For most functions, the Rosette output is very similar to the corresponding
SMT-LIB function with minor adjustments for syntax.

.. literalinclude:: /generated/functional/rosette.diff
   :language: diff
   :caption: portion of ``Functional::AbstractVisitor`` implementation diff showing similarities
   :start-at: SExpr logical_shift_left
   :end-at: "list-set-bv"

However there are some differences in the two formats with regards to how
booleans are handled, with Rosette providing built-in functions for conversion.

.. literalinclude:: /generated/functional/rosette.diff
   :language: diff
   :caption: portion of ``Functional::AbstractVisitor`` implementation diff showing differences
   :start-at: SExpr from_bool
   :end-before: SExpr extract

Of note here is the rare instance of the Rosette implementation *gaining* static
typing rather than losing it.  Where SMT_LIB calls zero/sign extension with the
number of extra bits needed (given by ``out_width - a.width()``), Rosette
instead specifies the type of the output (given by ``list("bitvector",
out_width)``).

.. literalinclude:: /generated/functional/rosette.diff
   :language: diff
   :caption: zero/sign extension implementation diff
   :start-after: SExpr buf(
   :end-before: SExpr concat(
   :lines: 2-3, 5-6

.. note:: Be sure to check the source code for the full list of differences here.

Module
~~~~~~

With most of the supporting classes out of the way, we now reach our three main
steps from the `minimal backend`_.  These are all handled by the ``SmtModule``
class, with the mapping from RTLIL module to FunctionalIR happening in the
constructor.  Each of the three ``SmtStruct``\ s; inputs, outputs, and state;
are also created in the constructor, with each value in the corresponding lists
in the IR being ``insert``\ ed.

.. literalinclude:: /generated/functional/smtlib.cc
   :language: c++
   :caption: ``SmtModule`` constructor
   :start-at: SmtModule(Module
   :end-at: }

Since Racket uses the ``-`` to access struct fields, the ``SmtrModule`` instead
uses an underscore for the name of the initial state.

.. literalinclude:: /generated/functional/rosette.diff
   :language: diff
   :caption: diff of ``Module`` constructor
   :start-at: scope.reserve(name
   :end-before: for (auto input

The ``write`` method is then responsible for writing the FunctionalIR to the
output file, formatted for the corresponding backend. ``SmtModule::write()``
breaks the output file down into four parts: defining the three structs,
declaring the ``pair`` datatype, defining the transfer function ``(inputs,
current_state) -> (outputs, next_state)`` with ``write_eval``, and declaring the
initial state with ``write_initial``.  The only change for the ``SmtrModule`` is
that the ``pair`` declaration isn't needed.

.. literalinclude:: /generated/functional/rosette.diff
   :language: diff
   :caption: diff of ``Module::write()`` method
   :start-at: void write(std::ostream &out)
   :end-at: }

The ``write_eval`` method is where the FunctionalIR nodes, outputs, and next
state are handled.  Just as with the `minimal backend`_, we iterate over the
nodes with ``for(auto n : ir)``, and then use the ``Struct::write_value()``
method for the ``output_struct`` and ``state_struct`` to iterate over the
outputs and next state respectively.

.. literalinclude:: /generated/functional/smtlib.cc
   :language: c++
   :caption: iterating over FunctionalIR nodes in ``SmtModule::write_eval()``
   :start-at: for(auto n : ir)
   :end-at: }

The main differences between our two backends here are syntactical.  First we
change the ``define-fun`` for the Racket style ``define`` which drops the
explicitly typed inputs/outputs.  And then we change the final result from a
``pair`` to the native ``cons`` which acts in much the same way, returning both
the ``outputs`` and the ``next_state`` in a single variable.

.. literalinclude:: /generated/functional/rosette.diff
   :language: diff
   :caption: diff of ``Module::write_eval()`` transfer function declaration
   :start-at: w.open(list("define-fun"
   :end-at: w.open(list("define"

.. literalinclude:: /generated/functional/rosette.diff
   :language: diff
   :caption: diff of output/next state handling ``Module::write_eval()``
   :start-at: w.open(list("pair"
   :end-at: w.pop();

For the ``write_initial`` method, the SMT-LIB backend uses ``declare-const`` and
``assert``\ s which must always hold true.  For Rosette we instead define the
initial state as any other variable that can be used by external code.  This
variable, ``[name]_initial``, can then be used in the ``[name]`` function call;
allowing the Rosette code to be used in the generation of the ``next_state``,
whereas the SMT-LIB code can only verify that a given ``next_state`` is correct.

.. literalinclude:: /generated/functional/rosette.diff
   :language: diff
   :caption: diff of ``Module::write_initial()`` method
   :start-at: void write_initial
   :end-before: void write

Backend
~~~~~~~

The final part is the ``Backend`` itself, with much of the same boiler plate as
the `minimal backend`_.  The main difference is that we use the `Module`_ to
perform the actual processing.

.. literalinclude:: /generated/functional/smtlib.cc
   :language: c++
   :caption: The ``FunctionalSmtBackend``
   :start-at: struct FunctionalSmtBackend
   :end-at: } FunctionalSmtBackend;

There are two additions here for Rosette.  The first is that the output file
needs to start with the ``#lang`` definition which tells the
compiler/interpreter that we want to use the Rosette language module.  The
second is that the `write_functional_rosette` command takes an optional
argument, ``-provides``.  If this argument is given, then the output file gets
an additional line declaring that everything in the file should be exported for
use; allowing the file to be treated as a Racket package with structs and
mapping function available for use externally.

.. literalinclude:: /generated/functional/rosette.diff
   :language: diff
   :caption: relevant portion of diff of ``Backend::execute()`` method
   :start-at: lang rosette/safe
   :end-before: for (auto module
