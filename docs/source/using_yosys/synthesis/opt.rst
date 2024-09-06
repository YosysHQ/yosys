Optimization passes
===================

Yosys employs a number of optimizations to generate better and cleaner results.
This chapter outlines these optimizations.

.. todo:: "outlines these optimizations" or "outlines *some*.."?

The `opt` macro command
--------------------------------

The Yosys pass `opt` runs a number of simple optimizations. This includes
removing unused signals and cells and const folding. It is recommended to run
this pass after each major step in the synthesis script.  As listed in
:doc:`/cmd/opt`, this macro command calls the following ``opt_*`` commands:

.. literalinclude:: /code_examples/macro_commands/opt.ys
   :language: yoscrypt
   :start-after: #end:
   :caption: Passes called by `opt`

.. _adv_opt_expr:

Constant folding and simple expression rewriting - `opt_expr`
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. todo:: unsure if this is too much detail and should be in :doc:`/yosys_internals/index`

This pass performs constant folding on the internal combinational cell types
described in :doc:`/cell_index`. This means a cell with all
constant inputs is replaced with the constant value this cell drives. In some
cases this pass can also optimize cells with some constant inputs.

.. table:: Const folding rules for `$_AND_` cells as used in `opt_expr`.
   :name: tab:opt_expr_and
   :align: center

   ========= ========= ===========
   A-Input   B-Input   Replacement
   ========= ========= ===========
   any       0         0
   0         any       0
   1         1         1
   --------- --------- -----------
   X/Z       X/Z       X
   1         X/Z       X
   X/Z       1         X
   --------- --------- -----------
   any       X/Z       0
   X/Z       any       0
   --------- --------- -----------
   :math:`a` 1         :math:`a`
   1         :math:`b` :math:`b`
   ========= ========= ===========

:numref:`Table %s <tab:opt_expr_and>` shows the replacement rules used for
optimizing an `$_AND_` gate. The first three rules implement the obvious const
folding rules. Note that 'any' might include dynamic values calculated by other
parts of the circuit. The following three lines propagate undef (X) states.
These are the only three cases in which it is allowed to propagate an undef
according to Sec. 5.1.10 of IEEE Std. 1364-2005 :cite:p:`Verilog2005`.

The next two lines assume the value 0 for undef states. These two rules are only
used if no other substitutions are possible in the current module. If other
substitutions are possible they are performed first, in the hope that the 'any'
will change to an undef value or a 1 and therefore the output can be set to
undef.

The last two lines simply replace an `$_AND_` gate with one constant-1 input
with a buffer.

Besides this basic const folding the `opt_expr` pass can replace 1-bit wide
`$eq` and `$ne` cells with buffers or not-gates if one input is constant.
Equality checks may also be reduced in size if there are redundant bits in the
arguments (i.e. bits which are constant on both inputs).  This can, for example,
result in a 32-bit wide constant like ``255`` being reduced to the 8-bit value
of ``8'11111111`` if the signal being compared is only 8-bit as in
:ref:`addr_gen_clean` of :doc:`/getting_started/example_synth`.

The `opt_expr` pass is very conservative regarding optimizing `$mux` cells, as
these cells are often used to model decision-trees and breaking these trees can
interfere with other optimizations.

.. literalinclude:: /code_examples/opt/opt_expr.ys
   :language: Verilog
   :start-after: read_verilog <<EOT
   :end-before: EOT
   :caption: example verilog for demonstrating `opt_expr`

.. figure:: /_images/code_examples/opt/opt_expr.*
   :class: width-helper invert-helper

   Before and after `opt_expr`

Merging identical cells - `opt_merge`
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This pass performs trivial resource sharing. This means that this pass
identifies cells with identical inputs and replaces them with a single instance
of the cell.

The option ``-nomux`` can be used to disable resource sharing for multiplexer
cells (`$mux` and `$pmux`.) This can be useful as it prevents multiplexer trees
to be merged, which might prevent `opt_muxtree` to identify possible
optimizations.

.. literalinclude:: /code_examples/opt/opt_merge.ys
   :language: Verilog
   :start-after: read_verilog <<EOT
   :end-before: EOT
   :caption: example verilog for demonstrating `opt_merge`

.. figure:: /_images/code_examples/opt/opt_merge.*
   :class: width-helper invert-helper

   Before and after `opt_merge`

Removing never-active branches from multiplexer tree - `opt_muxtree`
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This pass optimizes trees of multiplexer cells by analyzing the select inputs.
Consider the following simple example:

.. literalinclude:: /code_examples/opt/opt_muxtree.ys
   :language: Verilog
   :start-after: read_verilog <<EOT
   :end-before: EOT
   :caption: example verilog for demonstrating `opt_muxtree`

The output can never be ``c``, as this would require ``a`` to be 1 for the outer
multiplexer and 0 for the inner multiplexer. The `opt_muxtree` pass detects this
contradiction and replaces the inner multiplexer with a constant 1, yielding the
logic for ``y = a ? b : d``.

.. figure:: /_images/code_examples/opt/opt_muxtree.*
   :class: width-helper invert-helper

   Before and after `opt_muxtree`

Simplifying large MUXes and AND/OR gates - `opt_reduce`
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This is a simple optimization pass that identifies and consolidates identical
input bits to `$reduce_and` and `$reduce_or` cells. It also sorts the input bits
to ease identification of shareable `$reduce_and` and `$reduce_or` cells in
other passes.

This pass also identifies and consolidates identical inputs to multiplexer
cells. In this case the new shared select bit is driven using a `$reduce_or`
cell that combines the original select bits.

Lastly this pass consolidates trees of `$reduce_and` cells and trees of
`$reduce_or` cells to single large `$reduce_and` or `$reduce_or` cells.

These three simple optimizations are performed in a loop until a stable result
is produced.

Merging mutually exclusive cells with shared inputs - `opt_share`
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This pass identifies mutually exclusive cells of the same type that:
   a. share an input signal, and
   b. drive the same `$mux`, `$_MUX_`, or `$pmux` multiplexing cell,

allowing the cell to be merged and the multiplexer to be moved from multiplexing
its output to multiplexing the non-shared input signals.

.. literalinclude:: /code_examples/opt/opt_share.ys
   :language: Verilog
   :start-after: read_verilog <<EOT
   :end-before: EOT
   :caption: example verilog for demonstrating `opt_share`

.. figure:: /_images/code_examples/opt/opt_share.*
   :class: width-helper invert-helper

   Before and after `opt_share`

When running `opt` in full, the original `$mux` (labeled ``$3``) is optimized
away by `opt_expr`.

Performing DFF optimizations - `opt_dff`
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. todo:: ``$_DFF_`` isn't a valid cell

This pass identifies single-bit d-type flip-flops (`$_DFF_`, `$dff`, and `$adff`
cells) with a constant data input and replaces them with a constant driver.  It
can also merge clock enables and synchronous reset multiplexers, removing unused
control inputs.

Called with ``-nodffe`` and ``-nosdff``, this pass is used to prepare a design
for :doc:`/using_yosys/synthesis/fsm`.

Removing unused cells and wires - `opt_clean` pass
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This pass identifies unused signals and cells and removes them from the design.
It also creates an ``unused_bits`` attribute on wires with unused bits. This
attribute can be used for debugging or by other optimization passes.

When to use `opt` or `clean`
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Usually it does not hurt to call `opt` after each regular command in the
synthesis script. But it increases the synthesis time, so it is favourable to
only call `opt` when an improvement can be achieved.

It is generally a good idea to call `opt` before inherently expensive commands
such as `sat` or `freduce`, as the possible gain is much higher in these cases
as the possible loss.

The `clean` command, which is an alias for `opt_clean` with fewer outputs, on
the other hand is very fast and many commands leave a mess (dangling signal
wires, etc). For example, most commands do not remove any wires or cells. They
just change the connections and depend on a later call to clean to get rid of
the now unused objects. So the occasional ``;;``, which itself is an alias for
`clean`, is a good idea in every synthesis script, e.g:

.. code-block:: yoscrypt

   hierarchy; proc; opt; memory; opt_expr;; fsm;;

Other optimizations
-------------------

.. todo:: more on the other optimizations

- :doc:`/cmd/wreduce`
- :doc:`/cmd/peepopt`
- :doc:`/cmd/share`
- `abc` and `abc9`, see also: :doc:`abc`.
