Writing a new backend using FunctionalIR
===========================================

To simplify the writing of backends for functional languages or similar targets, Yosys provides an alternative intermediate representation called FunctionalIR which maps more directly on those targets.

FunctionalIR represents the design as a function `(inputs, current_state) -> (outputs, next_state)`.
This function is broken down into a series of assignments to variables.
Those assignments only use simple operations, like a simple addition.
Unlike RTLIL cells there is no support for automatically extending operands, every sign and zero extension has to be encoded as a separate operation.

Like SSA form, each variable is assigned to exactly once.
We can thus treat variables and assignments as equivalent and, since this is a graph-like representation, those variables are also called "nodes".
Unlike RTLIL's cells and wires representation, this representation is strictly ordered (topologically sorted) with definitions preceding their use.

Nodes are strongly typed, the two types (also called "sorts") available are
- `bit[n]` for an `n`-bit bitvector, and
- `memory[n,m]` for an immutable array of `2**n` values of type `bit[m]`.

In terms of actual code, Yosys provides a class `Functional::IR` that represents a design in FunctionalIR.
`Functional::IR::from_module` generates an instance from an RTLIL module.
The entire design is stored as a whole in an internal data structure.
To access the design, the `Functional::Node` class provides a reference to a particular node in the design.
The `Functional::IR` class supports the syntax `for(auto node : ir)` to iterate over every node.

`Functional::IR` also keeps track of inputs, outputs and "states" (registers and memories).
They all have a name (equal to their name in RTLIL), a sort and a "type".
The "type" field usually remains as the default value `$input`, `$output` or `$state`, however some RTLIL cells such as `$assert` or `$anyseq` generate auxiliary inputs/outputs/states that are given a different type to distinguish them from ordinary RTLIL inputs/outputs/states.
- To access an individual input/output/"state", use `ir.input(name, type)`, `ir.output(name, type)` or `ir.state(name, type)`. `type` defaults to the default type.
- To iterate over all inputs/outputs/"states" of a certain "type", methods `ir.inputs`, `ir.outputs`, `ir.states` are provided. Their argument defaults to the default types mentioned.
- To iterate over inputs/outputs/"states" of any "type", use `ir.all_inputs`, `ir.all_outputs` and `ir.all_states`.
- Outputs have a node that indicate the value of the output, this can be retrieved via `output.value()`.
- States have a node that indicate the next value of the state, this can be retrieved via `state.next_value()`.
  They also have an initial value that is accessed as either `state.initial_value_signal()` or `state.initial_value_memory()`, depending on their sort.

Each node has a "function", which defines its operation (for a complete list of functions and a specification of their operation, see `functional.h`).
Functions are represented as an enum `Functional::Fn` and the function field can be accessed as `node.fn()`.
Since the most common operation is a switch over the function that also accesses the arguments, the `Node` class provides a method `visit` that implements the visitor pattern.
For example, for an addition node `node` with arguments `n1` and `n2`, `node.visit(visitor)` would call `visitor.add(node, n1, n2)`.
Thus typically one would implement class with a method for every function.
Visitors should inherit from either `Functional::AbstractVisitor<ReturnType>` or `Functional::DefaultVisitor<ReturnType>`.
The former will produce a compiler error if a case is unhandled, the latter will call `default_handler(node)` instead.
Visitor methods should be marked as `override` to provide compiler errors if the arguments are wrong.