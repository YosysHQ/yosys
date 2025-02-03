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

Example: Adapting SMT-LIB backend for Rosette
---------------------------------------------

This section will walk through the process of adapting the SMT-LIB functional
backend (`write_functional_smt2`) to work with another s-expression target,
`Rosette`_.

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

Full code listings for the initial SMT-LIB backend and the converted Rosette
backend are included in the Yosys source repository under
:file:`backends/functional` as ``smtlib.cc`` and ``smtlib_rosette.cc``
respectively.  Note that the Rosette language is an extension of the Racket
language; this guide tends to refer to Racket when talking about the underlying
semantics/syntax of the language.

Scope
~~~~~

As described above, the ``Functional::Scope`` class is derived in order to avoid
collisions between identifiers in the generated output.  We switch out ``Smt``
in the class name for ``Smtr`` for ``smtlib_rosette``; which will happen through
the rest of the code too.  We also update the ``is_character_legal`` method to
reject ascii characters which are not allowed in Racket variable names.

.. literalinclude:: /code_examples/functional/rosette.diff
   :language: diff
   :caption: diff of ``Scope`` close
   :start-at: -struct SmtScope : public Functional::Scope<int> {
   :end-at: };

For the reserved keywords we trade the SMT-LIB specification for Racket to
prevent parts of our design from accidentally being treated as Racket code. We
also no longer need to reserve ``pair``, ``first``, and ``second``.  In
`write_functional_smt2` these are used for combining the ``(inputs,
current_state)`` and ``(outputs, next_state)`` into a single variable.  Racket
provides this functionality natively with ``cons``, which we will see later.

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

Note that we skip over the actual list of reserved keywords from both the smtlib
and racket specifications to save on space in this document.

Sort
~~~~

The ``Sort`` class is a wrapper for the ``Functional::Sort`` class, providing
the additional functionality of mapping variable declarations to s-expressions
with the ``to_sexpr()`` method.  The main change from ``SmtSort`` to
``SmtrSort`` is a syntactical one with signals represented as ``bitvector``\
s, and memories as ``list``\ s of signals.

.. literalinclude:: /code_examples/functional/rosette.diff
   :language: diff
   :caption: diff of ``Sort`` wrapper
   :start-at: SExpr to_sexpr() const {
   :end-before: };

Struct
~~~~~~

The SMT-LIB backend uses a class, ``SmtStruct``, to help with describing the
input, output, and state data structs.  Where each struct in the SMT-LIB output
is a new ``datatype`` with each element having its type declared using the
`Sort`_ above, in Rosette we use the native ``struct`` with each field only
being referred to by name.  For ease of use, we include comments for each field
to indicate the expected type.

.. literalinclude:: /code_examples/functional/rosette.diff
   :language: diff
   :caption: diff of ``write_definition`` method
   :start-at: void write_definition
   :end-before: template<typename Fn> void write_value

Struct fields in Rosette are accessed as ``<struct_name>-<field_name>``, where
field names only need to be unique within the struct, while accessors are unique
within the module.  We thus modify the class constructor and ``insert`` method
to support this; providing one scope that is local to the struct
(``local_scope``) and one which is shared across the whole module
(``global_scope``).

.. literalinclude:: /code_examples/functional/rosette.diff
   :language: diff
   :caption: diff of struct constructor
   :start-at: -  SmtStruct(std::string name, SmtScope &scope)
   :end-before: void write_definition

For writing outputs/next state (the ``write_value`` method), the only change is
to remove the check for zero-argument constructors since this is not necessary
with Rosette ``struct``\ s.

.. literalinclude:: /code_examples/functional/rosette.diff
   :language: diff
   :caption: diff of ``write_value`` method
   :start-at: template<typename Fn> void write_value
   :end-before: SExpr access

PrintVisitor
~~~~~~~~~~~~

The ``PrintVisitor`` implements the abstract ``Functional::AbstractVisitor``
class for converting FunctionalIR functions into s-expressions, including
reading inputs/current state.  For most functions, the Rosette output is very
similar to the corresponding SMT-LIB function with minor adjustments for syntax.

.. literalinclude:: /code_examples/functional/rosette.diff
   :language: diff
   :caption: portion of ``Functional::AbstractVisitor`` implementation diff showing similarities
   :start-at: SExpr zero_extend
   :end-at: SExpr sub

However there are some differences in the two formats with regards to how
booleans are handled, with Rosette providing built-in functions for conversion.

.. literalinclude:: /code_examples/functional/rosette.diff
   :language: diff
   :caption: portion of ``Functional::AbstractVisitor`` implementation diff showing differences
   :start-at: SExpr from_bool
   :end-before: SExpr extract

Module
~~~~~~

- map RTLIL module to FunctionalIR
- iterate over FunctionalIR and map to Rosette
   - defines the mapping function, ``(inputs, current_state) -> (outputs,
     next_state)``

Backend
~~~~~~~

- registers the `write_functional_rosette` command
- options (``-provides``)
   - allows file to be treated as a Racket package with structs and mapping
     function available for use externally

- opens and prepares file for writing
- iterates over modules in design
