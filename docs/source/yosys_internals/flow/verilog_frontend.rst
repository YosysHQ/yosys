.. _chapter:verilog:

The Verilog and AST frontends
=============================

This chapter provides an overview of the implementation of the Yosys Verilog and
AST frontends. The Verilog frontend reads Verilog-2005 code and creates an
abstract syntax tree (AST) representation of the input. This AST representation
is then passed to the AST frontend that converts it to RTLIL data, as
illustrated in :numref:`Fig. %s <fig:Verilog_flow>`.

.. figure:: /_images/internals/verilog_flow.*
	:class: width-helper invert-helper
	:name: fig:Verilog_flow

	Simplified Verilog to RTLIL data flow

Transforming Verilog to AST
---------------------------

The Verilog frontend converts the Verilog sources to an internal AST
representation that closely resembles the structure of the original Verilog
code. The Verilog frontend consists of three components, the Preprocessor, the
Lexer and the Parser.

The source code to the Verilog frontend can be found in
:file:`frontends/verilog/` in the Yosys source tree.

The Verilog preprocessor
~~~~~~~~~~~~~~~~~~~~~~~~

The Verilog preprocessor scans over the Verilog source code and interprets some
of the Verilog compiler directives such as :literal:`\`include`,
:literal:`\`define` and :literal:`\`ifdef`.

It is implemented as a C++ function that is passed a file descriptor as input
and returns the pre-processed Verilog code as a ``std::string``.

The source code to the Verilog Preprocessor can be found in
:file:`frontends/verilog/preproc.cc` in the Yosys source tree.

The Verilog lexer
~~~~~~~~~~~~~~~~~

The Verilog Lexer is written using the lexer generator flex. Its source code can
be found in :file:`frontends/verilog/verilog_lexer.l` in the Yosys source tree.
The lexer does little more than identifying all keywords and literals recognised
by the Yosys Verilog frontend.

The lexer keeps track of the current location in the Verilog source code using
some global variables. These variables are used by the constructor of AST nodes
to annotate each node with the source code location it originated from.

Finally the lexer identifies and handles special comments such as "``// synopsys
translate_off``" and "``// synopsys full_case``". (It is recommended to use
:literal:`\`ifdef` constructs instead of the Synsopsys translate_on/off comments
and attributes such as ``(* full_case *)`` over "``// synopsys full_case``"
whenever possible.)

The Verilog parser
~~~~~~~~~~~~~~~~~~

The Verilog Parser is written using the parser generator bison. Its source code
can be found in :file:`frontends/verilog/verilog_parser.y` in the Yosys source
tree.

It generates an AST using the ``AST::AstNode`` data structure defined in
:file:`frontends/ast/ast.h`. An ``AST::AstNode`` object has the following
properties:

.. list-table:: AST node types with their corresponding Verilog constructs.
    :name: tab:Verilog_AstNodeType
    :widths: 50 50

    * - AST Node Type
      - Corresponding Verilog Construct
    * - AST_NONE
      - This Node type should never be used.
    * - AST_DESIGN
      - This node type is used for the top node of the AST tree. It has no
        corresponding Verilog construct.
    * - AST_MODULE, AST_TASK, AST_FUNCTION
      - ``module``, ``task`` and ``function``
    * - AST_WIRE
      - ``input``, ``output``, ``wire``, ``reg`` and ``integer``
    * - AST_MEMORY
      - Verilog Arrays
    * - AST_AUTOWIRE
      - Created by the simplifier when an undeclared signal name is used.
    * - AST_PARAMETER, AST_LOCALPARAM
      - ``parameter`` and ``localparam``
    * - AST_PARASET
      - Parameter set in cell instantiation
    * - AST_ARGUMENT
      - Port connection in cell instantiation
    * - AST_RANGE
      - Bit-Index in a signal or element index in array
    * - AST_CONSTANT
      - A literal value
    * - AST_CELLTYPE
      - The type of cell in cell instantiation
    * - AST_IDENTIFIER
      - An Identifier (signal name in expression or cell/task/etc. name in other
        contexts)
    * - AST_PREFIX
      - Construct an identifier in the form <prefix>[<index>].<suffix> (used
        only in advanced generate constructs)
    * - AST_FCALL, AST_TCALL
      - Call to function or task
    * - AST_TO_SIGNED, AST_TO_UNSIGNED
      - The ``$signed()`` and ``$unsigned()`` functions
    * - AST_CONCAT, AST_REPLICATE
      - The ``{...}`` and ``{...{...}}`` operators
    * - AST_BIT_NOT, AST_BIT_AND, AST_BIT_OR, AST_BIT_XOR, AST_BIT_XNOR
      - The bitwise operators ``~``, ``&``, ``|``, ``^`` and ``~^``
    * - AST_REDUCE_AND, AST_REDUCE_OR, AST_REDUCE_XOR, AST_REDUCE_XNOR
      - The unary reduction operators ``~``, ``&``, ``|``, ``^`` and ``~^``
    * - AST_REDUCE_BOOL
      - Conversion from multi-bit value to boolean value (equivalent to
        AST_REDUCE_OR)
    * - AST_SHIFT_LEFT, AST_SHIFT_RIGHT, AST_SHIFT_SLEFT, AST_SHIFT_SRIGHT
      - The shift operators ``<<``, ``>>``, ``<<<`` and ``>>>``
    * - AST_LT, AST_LE, AST_EQ, AST_NE, AST_GE, AST_GT
      - The relational operators ``<``, ``<=``, ``==``, ``!=``, ``>=`` and ``>``
    * - AST_ADD, AST_SUB, AST_MUL, AST_DIV, AST_MOD, AST_POW
      - The binary operators ``+``, ``-``, ``*``, ``/``, ``%`` and ``**``
    * - AST_POS, AST_NEG
      - The prefix operators ``+`` and ``-``
    * - AST_LOGIC_AND, AST_LOGIC_OR, AST_LOGIC_NOT
      - The logic operators ``&&``, ``||`` and ``!``
    * - AST_TERNARY
      - The ternary ``?:``-operator
    * - AST_MEMRD AST_MEMWR
      - Read and write memories. These nodes are generated by the AST simplifier
        for writes/reads to/from Verilog arrays.
    * - AST_ASSIGN
      - An ``assign`` statement
    * - AST_CELL
      - A cell instantiation
    * - AST_PRIMITIVE
      - A primitive cell (``and``, ``nand``, ``or``, etc.)
    * - AST_ALWAYS, AST_INITIAL
      - Verilog ``always``- and ``initial``-blocks
    * - AST_BLOCK
      - A ``begin``-``end``-block
    * - AST_ASSIGN_EQ. AST_ASSIGN_LE
      - Blocking (``=``) and nonblocking (``<=``) assignments within an
        ``always``- or ``initial``-block
    * - AST_CASE. AST_COND, AST_DEFAULT
      - The ``case`` (``if``) statements, conditions within a case and the
        default case respectively
    * - AST_FOR
      - A ``for``-loop with an ``always``- or ``initial``-block
    * - AST_GENVAR, AST_GENBLOCK, AST_GENFOR, AST_GENIF
      - The ``genvar`` and ``generate`` keywords and ``for`` and ``if`` within a
        generate block.
    * - AST_POSEDGE, AST_NEGEDGE, AST_EDGE
      - Event conditions for ``always`` blocks.

-  | The node type
   | This enum (``AST::AstNodeType``) specifies the role of the node.
     :numref:`Table %s <tab:Verilog_AstNodeType>` contains a list of all node
     types.

-  | The child nodes
   | This is a list of pointers to all children in the abstract syntax tree.

-  | Attributes
   | As almost every AST node might have Verilog attributes assigned to it, the
     ``AST::AstNode`` has direct support for attributes. Note that the attribute
     values are again AST nodes.

-  | Node content
   | Each node might have additional content data. A series of member variables
     exist to hold such data. For example the member ``std::string str`` can
     hold a string value and is used e.g. in the ``AST_IDENTIFIER`` node type to
     store the identifier name.

-  | Source code location
   | Each ``AST::AstNode`` is automatically annotated with the current source
     code location by the ``AST::AstNode`` constructor. It is stored in the
     ``std::string filename`` and ``int linenum`` member variables.

The ``AST::AstNode`` constructor can be called with up to two child nodes that
are automatically added to the list of child nodes for the new object. This
simplifies the creation of AST nodes for simple expressions a bit. For example
the bison code for parsing multiplications:

.. code:: none
   	:number-lines:

	basic_expr '*' attr basic_expr {
		$$ = new AstNode(AST_MUL, $1, $4);
		append_attr($$, $3);
	} |

The generated AST data structure is then passed directly to the AST frontend
that performs the actual conversion to RTLIL.

Note that the Yosys command ``read_verilog`` provides the options ``-yydebug``
and ``-dump_ast`` that can be used to print the parse tree or abstract syntax
tree respectively.

Transforming AST to RTLIL
-------------------------

The AST Frontend converts a set of modules in AST representation to modules in
RTLIL representation and adds them to the current design. This is done in two
steps: simplification and RTLIL generation.

The source code to the AST frontend can be found in ``frontends/ast/`` in the
Yosys source tree.

AST simplification
~~~~~~~~~~~~~~~~~~

A full-featured AST is too complex to be transformed into RTLIL directly.
Therefore it must first be brought into a simpler form. This is done by calling
the ``AST::AstNode::simplify()`` method of all ``AST_MODULE`` nodes in the AST.
This initiates a recursive process that performs the following transformations
on the AST data structure:

-  Inline all task and function calls.

-  Evaluate all ``generate``-statements and unroll all ``for``-loops.

-  Perform const folding where it is necessary (e.g. in the value part of
   ``AST_PARAMETER``, ``AST_LOCALPARAM``, ``AST_PARASET`` and ``AST_RANGE``
   nodes).

-  Replace ``AST_PRIMITIVE`` nodes with appropriate ``AST_ASSIGN`` nodes.

-  Replace dynamic bit ranges in the left-hand-side of assignments with
   ``AST_CASE`` nodes with ``AST_COND`` children for each possible case.

-  Detect array access patterns that are too complicated for the
   ``RTLIL::Memory`` abstraction and replace them with a set of signals and
   cases for all reads and/or writes.

-  Otherwise replace array accesses with ``AST_MEMRD`` and ``AST_MEMWR`` nodes.

In addition to these transformations, the simplifier also annotates the
AST with additional information that is needed for the RTLIL generator,
namely:

-  All ranges (width of signals and bit selections) are not only const
   folded but (when a constant value is found) are also written to
   member variables in the AST_RANGE node.

-  All identifiers are resolved and all ``AST_IDENTIFIER`` nodes are annotated
   with a pointer to the AST node that contains the declaration of the
   identifier. If no declaration has been found, an ``AST_AUTOWIRE`` node is
   created and used for the annotation.

This produces an AST that is fairly easy to convert to the RTLIL format.

Generating RTLIL
~~~~~~~~~~~~~~~~

After AST simplification, the ``AST::AstNode::genRTLIL()`` method of each
``AST_MODULE`` node in the AST is called. This initiates a recursive process
that generates equivalent RTLIL data for the AST data.

The ``AST::AstNode::genRTLIL()`` method returns an ``RTLIL::SigSpec`` structure.
For nodes that represent expressions (operators, constants, signals, etc.), the
cells needed to implement the calculation described by the expression are
created and the resulting signal is returned. That way it is easy to generate
the circuits for large expressions using depth-first recursion. For nodes that
do not represent an expression (such as ``AST_CELL``), the corresponding circuit
is generated and an empty ``RTLIL::SigSpec`` is returned.

Synthesizing Verilog always blocks
--------------------------------------

For behavioural Verilog code (code utilizing ``always``- and ``initial``-blocks)
it is necessary to also generate ``RTLIL::Process`` objects. This is done in the
following way:

Whenever ``AST::AstNode::genRTLIL()`` encounters an ``always``- or
``initial``-block, it creates an instance of ``AST_INTERNAL::ProcessGenerator``.
This object then generates the ``RTLIL::Process`` object for the block. It also
calls ``AST::AstNode::genRTLIL()`` for all right-hand-side expressions contained
within the block.

First the ``AST_INTERNAL::ProcessGenerator`` creates a list of all signals
assigned within the block. It then creates a set of temporary signals using the
naming scheme ``$ <number> \ <original_name>`` for each of the assigned signals.

Then an ``RTLIL::Process`` is created that assigns all intermediate values for
each left-hand-side signal to the temporary signal in its
``RTLIL::CaseRule``/``RTLIL::SwitchRule`` tree.

Finally a ``RTLIL::SyncRule`` is created for the ``RTLIL::Process`` that assigns
the temporary signals for the final values to the actual signals.

A process may also contain memory writes. A ``RTLIL::MemWriteAction`` is created
for each of them.

Calls to ``AST::AstNode::genRTLIL()`` are generated for right hand sides as
needed. When blocking assignments are used, ``AST::AstNode::genRTLIL()`` is
configured using global variables to use the temporary signals that hold the
correct intermediate values whenever one of the previously assigned signals is
used in an expression.

Unfortunately the generation of a correct
``RTLIL::CaseRule``/\ ``RTLIL::SwitchRule`` tree for behavioural code is a
non-trivial task. The AST frontend solves the problem using the approach
described on the following pages. The following example illustrates what the
algorithm is supposed to do. Consider the following Verilog code:

.. code:: verilog
   :number-lines:

   always @(posedge clock) begin
       out1 = in1;
       if (in2)
           out1 = !out1;
       out2 <= out1;
       if (in3)
           out2 <= out2;
       if (in4)
           if (in5)
               out3 <= in6;
           else
               out3 <= in7;
       out1 = out1 ^ out2;
   end

This is translated by the Verilog and AST frontends into the following RTLIL
code (attributes, cell parameters and wire declarations not included):

.. code:: RTLIL
   :number-lines:

   cell $logic_not $logic_not$<input>:4$2
     connect \A \in1
     connect \Y $logic_not$<input>:4$2_Y
   end
   cell $xor $xor$<input>:13$3
     connect \A $1\out1[0:0]
     connect \B \out2
     connect \Y $xor$<input>:13$3_Y
   end
   process $proc$<input>:1$1
     assign $0\out3[0:0] \out3
     assign $0\out2[0:0] $1\out1[0:0]
     assign $0\out1[0:0] $xor$<input>:13$3_Y
     switch \in2
       case 1'1
         assign $1\out1[0:0] $logic_not$<input>:4$2_Y
       case
         assign $1\out1[0:0] \in1
     end
     switch \in3
       case 1'1
         assign $0\out2[0:0] \out2
       case
     end
     switch \in4
       case 1'1
         switch \in5
           case 1'1
             assign $0\out3[0:0] \in6
           case
             assign $0\out3[0:0] \in7
         end
       case
     end
     sync posedge \clock
       update \out1 $0\out1[0:0]
       update \out2 $0\out2[0:0]
       update \out3 $0\out3[0:0]
   end

Note that the two operators are translated into separate cells outside the
generated process. The signal ``out1`` is assigned using blocking assignments
and therefore ``out1`` has been replaced with a different signal in all
expressions after the initial assignment. The signal ``out2`` is assigned using
nonblocking assignments and therefore is not substituted on the right-hand-side
expressions.

The ``RTLIL::CaseRule``/\ ``RTLIL::SwitchRule`` tree must be interpreted the
following way:

-  On each case level (the body of the process is the root case), first the
   actions on this level are evaluated and then the switches within the case are
   evaluated. (Note that the last assignment on line 13 of the Verilog code has
   been moved to the beginning of the RTLIL process to line 13 of the RTLIL
   listing.)

   I.e. the special cases deeper in the switch hierarchy override the defaults
   on the upper levels. The assignments in lines 12 and 22 of the RTLIL code
   serve as an example for this.

   Note that in contrast to this, the order within the ``RTLIL::SwitchRule``
   objects within a ``RTLIL::CaseRule`` is preserved with respect to the
   original AST and Verilog code.

-  The whole ``RTLIL::CaseRule``/\ ``RTLIL::SwitchRule`` tree describes an
   asynchronous circuit. I.e. the decision tree formed by the switches can be
   seen independently for each assigned signal. Whenever one assigned signal
   changes, all signals that depend on the changed signals are to be updated.
   For example the assignments in lines 16 and 18 in the RTLIL code in fact
   influence the assignment in line 12, even though they are in the "wrong
   order".

The only synchronous part of the process is in the ``RTLIL::SyncRule`` object
generated at line 35 in the RTLIL code. The sync rule is the only part of the
process where the original signals are assigned. The synchronization event from
the original Verilog code has been translated into the synchronization type
(posedge) and signal (``\clock``) for the ``RTLIL::SyncRule`` object. In the
case of this simple example the ``RTLIL::SyncRule`` object is later simply
transformed into a set of d-type flip-flops and the
``RTLIL::CaseRule``/\ ``RTLIL::SwitchRule`` tree to a decision tree using
multiplexers.

In more complex examples (e.g. asynchronous resets) the part of the
``RTLIL::CaseRule``/\ ``RTLIL::SwitchRule`` tree that describes the asynchronous
reset must first be transformed to the correct ``RTLIL::SyncRule`` objects. This
is done by the ``proc_arst`` pass.

The ProcessGenerator algorithm
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The ``AST_INTERNAL::ProcessGenerator`` uses the following internal state
variables:

-  | ``subst_rvalue_from`` and ``subst_rvalue_to``
   | These two variables hold the replacement pattern that should be used by
     ``AST::AstNode::genRTLIL()`` for signals with blocking assignments. After
    initialization of ``AST_INTERNAL::ProcessGenerator`` these two variables are
    empty.

-  | ``subst_lvalue_from`` and ``subst_lvalue_to`` 
   | These two variables contain the mapping from left-hand-side signals (``\
     <name>``) to the current temporary signal for the same thing (initially
     ``$0\ <name>``).

-  | ``current_case`` 
   | A pointer to a ``RTLIL::CaseRule`` object. Initially this is the root case
     of the generated ``RTLIL::Process``.

As the algorithm runs these variables are continuously modified as well as
pushed to the stack and later restored to their earlier values by popping from
the stack.

On startup the ProcessGenerator generates a new ``RTLIL::Process`` object with
an empty root case and initializes its state variables as described above. Then
the ``RTLIL::SyncRule`` objects are created using the synchronization events
from the AST_ALWAYS node and the initial values of ``subst_lvalue_from`` and
``subst_lvalue_to``. Then the AST for this process is evaluated recursively.

During this recursive evaluation, three different relevant types of AST nodes
can be discovered: ``AST_ASSIGN_LE`` (nonblocking assignments),
``AST_ASSIGN_EQ`` (blocking assignments) and ``AST_CASE`` (``if`` or ``case``
statement).

Handling of nonblocking assignments
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

When an ``AST_ASSIGN_LE`` node is discovered, the following actions are
performed by the ProcessGenerator:

-  The left-hand-side is evaluated using ``AST::AstNode::genRTLIL()`` and mapped
   to a temporary signal name using ``subst_lvalue_from`` and
   ``subst_lvalue_to``.

-  The right-hand-side is evaluated using ``AST::AstNode::genRTLIL()``. For this
   call, the values of ``subst_rvalue_from`` and ``subst_rvalue_to`` are used to
   map blocking-assigned signals correctly.

-  Remove all assignments to the same left-hand-side as this assignment from the
   ``current_case`` and all cases within it.

-  Add the new assignment to the ``current_case``.

Handling of blocking assignments
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

When an ``AST_ASSIGN_EQ`` node is discovered, the following actions are
performed by the ProcessGenerator:

-  Perform all the steps that would be performed for a nonblocking assignment
   (see above).

-  Remove the found left-hand-side (before lvalue mapping) from
   ``subst_rvalue_from`` and also remove the respective bits from
   ``subst_rvalue_to``.

-  Append the found left-hand-side (before lvalue mapping) to
   ``subst_rvalue_from`` and append the found right-hand-side to
   ``subst_rvalue_to``.

Handling of cases and if-statements
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

When an ``AST_CASE`` node is discovered, the following actions are performed by
the ProcessGenerator:

-  The values of ``subst_rvalue_from``, ``subst_rvalue_to``,
   ``subst_lvalue_from`` and ``subst_lvalue_to`` are pushed to the stack.

-  A new ``RTLIL::SwitchRule`` object is generated, the selection expression is
   evaluated using ``AST::AstNode::genRTLIL()`` (with the use of
   ``subst_rvalue_from`` and ``subst_rvalue_to``) and added to the
   ``RTLIL::SwitchRule`` object and the object is added to the ``current_case``.

-  All lvalues assigned to within the ``AST_CASE`` node using blocking
   assignments are collected and saved in the local variable
   ``this_case_eq_lvalue``.

-  New temporary signals are generated for all signals in
   ``this_case_eq_lvalue`` and stored in ``this_case_eq_ltemp``.

-  The signals in ``this_case_eq_lvalue`` are mapped using ``subst_rvalue_from``
   and ``subst_rvalue_to`` and the resulting set of signals is stored in
   ``this_case_eq_rvalue``.

Then the following steps are performed for each ``AST_COND`` node within the
``AST_CASE`` node:

-  Set ``subst_rvalue_from``, ``subst_rvalue_to``, ``subst_lvalue_from`` and
   ``subst_lvalue_to`` to the values that have been pushed to the stack.

-  Remove ``this_case_eq_lvalue`` from
   ``subst_lvalue_from``/``subst_lvalue_to``.

-  Append ``this_case_eq_lvalue`` to ``subst_lvalue_from`` and append
   ``this_case_eq_ltemp`` to ``subst_lvalue_to``.

-  Push the value of ``current_case``.

-  Create a new ``RTLIL::CaseRule``. Set ``current_case`` to the new object and
   add the new object to the ``RTLIL::SwitchRule`` created above.

-  Add an assignment from ``this_case_eq_rvalue`` to ``this_case_eq_ltemp`` to
   the new ``current_case``.

-  Evaluate the compare value for this case using
   ``AST::AstNode::genRTLIL()`` (with the use of ``subst_rvalue_from``
   and ``subst_rvalue_to``) modify the new ``current_case`` accordingly.

-  Recursion into the children of the ``AST_COND`` node.

-  Restore ``current_case`` by popping the old value from the stack.

Finally the following steps are performed:

-  The values of ``subst_rvalue_from``, ``subst_rvalue_to``,
   ``subst_lvalue_from`` and ``subst_lvalue_to`` are popped from the stack.

-  The signals from ``this_case_eq_lvalue`` are removed from the
   ``subst_rvalue_from``/``subst_rvalue_to``-pair.

-  The value of ``this_case_eq_lvalue`` is appended to ``subst_rvalue_from`` and
   the value of ``this_case_eq_ltemp`` is appended to ``subst_rvalue_to``.

-  Map the signals in ``this_case_eq_lvalue`` using
   ``subst_lvalue_from``/``subst_lvalue_to``.

-  Remove all assignments to signals in ``this_case_eq_lvalue`` in
   ``current_case`` and all cases within it.

-  Add an assignment from ``this_case_eq_ltemp`` to ``this_case_eq_lvalue`` to
   ``current_case``.

Further analysis of the algorithm for cases and if-statements
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

With respect to nonblocking assignments the algorithm is easy: later assignments
invalidate earlier assignments. For each signal assigned using nonblocking
assignments exactly one temporary variable is generated (with the ``$0``-prefix)
and this variable is used for all assignments of the variable.

Note how all the ``_eq_``-variables become empty when no blocking assignments
are used and many of the steps in the algorithm can then be ignored as a result
of this.

For a variable with blocking assignments the algorithm shows the following
behaviour: First a new temporary variable is created. This new temporary
variable is then registered as the assignment target for all assignments for
this variable within the cases for this ``AST_CASE`` node. Then for each case
the new temporary variable is first assigned the old temporary variable. This
assignment is overwritten if the variable is actually assigned in this case and
is kept as a default value otherwise.

This yields an ``RTLIL::CaseRule`` that assigns the new temporary variable in
all branches. So when all cases have been processed a final assignment is added
to the containing block that assigns the new temporary variable to the old one.
Note how this step always overrides a previous assignment to the old temporary
variable. Other than nonblocking assignments, the old assignment could still
have an effect somewhere in the design, as there have been calls to
``AST::AstNode::genRTLIL()`` with a
``subst_rvalue_from``/\ ``subst_rvalue_to``-tuple that contained the
right-hand-side of the old assignment.

The proc pass
~~~~~~~~~~~~~

The ProcessGenerator converts a behavioural model in AST representation to a
behavioural model in ``RTLIL::Process`` representation. The actual conversion
from a behavioural model to an RTL representation is performed by the
:cmd:ref:`proc` pass and the passes it launches:

-  | :cmd:ref:`proc_clean` and :cmd:ref:`proc_rmdead` 
   | These two passes just clean up the ``RTLIL::Process`` structure. The
     :cmd:ref:`proc_clean` pass removes empty parts (eg. empty assignments) from
     the process and :cmd:ref:`proc_rmdead` detects and removes unreachable
     branches from the process's decision trees.

-  | :cmd:ref:`proc_arst` 
   | This pass detects processes that describe d-type flip-flops with
     asynchronous resets and rewrites the process to better reflect what they
     are modelling: Before this pass, an asynchronous reset has two
     edge-sensitive sync rules and one top-level ``RTLIL::SwitchRule`` for the
     reset path. After this pass the sync rule for the reset is level-sensitive
     and the top-level ``RTLIL::SwitchRule`` has been removed.

-  | :cmd:ref:`proc_mux` 
   | This pass converts the ``RTLIL::CaseRule``/\ ``RTLIL::SwitchRule``-tree to a
     tree of multiplexers per written signal. After this, the ``RTLIL::Process``
     structure only contains the ``RTLIL::SyncRule`` s that describe the output
     registers.

-  | :cmd:ref:`proc_dff`
   | This pass replaces the ``RTLIL::SyncRule``\ s to d-type flip-flops (with
     asynchronous resets if necessary).

-  | :cmd:ref:`proc_dff`
   | This pass replaces the ``RTLIL::MemWriteAction``\ s with ``$memwr`` cells.

-  | :cmd:ref:`proc_clean`
   | A final call to :cmd:ref:`proc_clean` removes the now empty
     ``RTLIL::Process`` objects.

Performing these last processing steps in passes instead of in the Verilog
frontend has two important benefits:

First it improves the transparency of the process. Everything that happens in a
separate pass is easier to debug, as the RTLIL data structures can be easily
investigated before and after each of the steps.

Second it improves flexibility. This scheme can easily be extended to support
other types of storage-elements, such as sr-latches or d-latches, without having
to extend the actual Verilog frontend.

.. todo:: Synthesizing Verilog arrays

  Add some information on the generation of ``$memrd`` and ``$memwr`` cells and
  how they are processed in the memory pass.


.. todo:: Synthesizing parametric designs

  Add some information on the ``RTLIL::Module::derive()`` method and how it is
  used to synthesize parametric modules via the hierarchy pass.
