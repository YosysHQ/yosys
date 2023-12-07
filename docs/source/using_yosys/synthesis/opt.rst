Optimization passes
===================

.. todo:: check text context, also check the optimization passes still do what they say

Yosys employs a number of optimizations to generate better and cleaner results.
This chapter outlines these optimizations.

The :cmd:ref:`opt` pass
--------------------------

The Yosys pass :cmd:ref:`opt` runs a number of simple optimizations. This
includes removing unused signals and cells and const folding. It is recommended
to run this pass after each major step in the synthesis script. At the time of
this writing the :cmd:ref:`opt` pass executes the following passes that each
perform a simple optimization:

.. code-block:: yoscrypt

    opt_expr                # const folding and simple expression rewriting
    opt_merge -nomux        # merging identical cells

    do
        opt_muxtree         # remove never-active branches from multiplexer tree
        opt_reduce          # consolidate trees of boolean ops to reduce functions
        opt_merge           # merging identical cells
        opt_rmdff           # remove/simplify registers with constant inputs
        opt_clean           # remove unused objects (cells, wires) from design
        opt_expr            # const folding and simple expression rewriting
    while [changed design]

The command :cmd:ref:`clean` can be used as alias for :cmd:ref:`opt_clean`. And
``;;`` can be used as shortcut for :cmd:ref:`clean`. For example:

.. code-block:: yoscrypt

    hierarchy; proc; opt; memory; opt_expr;; fsm;;

The :cmd:ref:`opt_expr` pass
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This pass performs const folding on the internal combinational cell types
described in :doc:`/yosys_internals/formats/cell_library`. This means a cell
with all constant inputs is replaced with the constant value this cell drives.
In some cases this pass can also optimize cells with some constant inputs.

.. table:: Const folding rules for ``$_AND_`` cells as used in :cmd:ref:`opt_expr`.
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

.. todo:: How to format table?

:numref:`Table %s <tab:opt_expr_and>` shows the replacement rules used for
optimizing an ``$_AND_`` gate. The first three rules implement the obvious const
folding rules. Note that 'any' might include dynamic values calculated by other
parts of the circuit. The following three lines propagate undef (X) states.
These are the only three cases in which it is allowed to propagate an undef
according to Sec. 5.1.10 of IEEE Std. 1364-2005 :cite:p:`Verilog2005`.

The next two lines assume the value 0 for undef states. These two rules are only
used if no other substitutions are possible in the current module. If other
substitutions are possible they are performed first, in the hope that the 'any'
will change to an undef value or a 1 and therefore the output can be set to
undef.

The last two lines simply replace an ``$_AND_`` gate with one constant-1 input
with a buffer.

Besides this basic const folding the :cmd:ref:`opt_expr` pass can replace 1-bit
wide ``$eq`` and ``$ne`` cells with buffers or not-gates if one input is
constant.

The :cmd:ref:`opt_expr` pass is very conservative regarding optimizing ``$mux``
cells, as these cells are often used to model decision-trees and breaking these
trees can interfere with other optimizations.

The :cmd:ref:`opt_muxtree` pass
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This pass optimizes trees of multiplexer cells by analyzing the select inputs.
Consider the following simple example:

.. code:: verilog

   module uut(a, y); 
      input a; 
      output [1:0] y = a ? (a ? 1 : 2) : 3; 
   endmodule

The output can never be 2, as this would require ``a`` to be 1 for the outer
multiplexer and 0 for the inner multiplexer. The :cmd:ref:`opt_muxtree` pass
detects this contradiction and replaces the inner multiplexer with a constant 1,
yielding the logic for ``y = a ? 1 : 3``.

The :cmd:ref:`opt_reduce` pass
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This is a simple optimization pass that identifies and consolidates identical
input bits to ``$reduce_and`` and ``$reduce_or`` cells. It also sorts the input
bits to ease identification of shareable ``$reduce_and`` and ``$reduce_or``
cells in other passes.

This pass also identifies and consolidates identical inputs to multiplexer
cells. In this case the new shared select bit is driven using a ``$reduce_or``
cell that combines the original select bits.

Lastly this pass consolidates trees of ``$reduce_and`` cells and trees of
``$reduce_or`` cells to single large ``$reduce_and`` or ``$reduce_or`` cells.

These three simple optimizations are performed in a loop until a stable result
is produced.

The ``opt_rmdff`` pass
~~~~~~~~~~~~~~~~~~~~~~

.. todo:: Update to ``opt_dff``

This pass identifies single-bit d-type flip-flops (``$_DFF_``, ``$dff``, and
``$adff`` cells) with a constant data input and replaces them with a constant
driver.

The :cmd:ref:`opt_clean` pass
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This pass identifies unused signals and cells and removes them from the design.
It also creates an ``\unused_bits`` attribute on wires with unused bits. This
attribute can be used for debugging or by other optimization passes.

The :cmd:ref:`opt_merge` pass
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This pass performs trivial resource sharing. This means that this pass
identifies cells with identical inputs and replaces them with a single instance
of the cell.

The option ``-nomux`` can be used to disable resource sharing for multiplexer
cells (``$mux`` and ``$pmux``.) This can be useful as it prevents multiplexer
trees to be merged, which might prevent :cmd:ref:`opt_muxtree` to identify
possible optimizations.

Example
~~~~~~~

.. todo:: describe ``opt`` images

.. figure:: /_images/code_examples/synth_flow/opt_01.*
   :class: width-helper

.. literalinclude:: /code_examples/synth_flow/opt_01.ys
   :language: yoscrypt
   :caption: ``docs/source/code_examples/synth_flow/opt_01.ys``

.. literalinclude:: /code_examples/synth_flow/opt_01.v
   :language: verilog
   :caption: ``docs/source/code_examples/synth_flow/opt_01.v``

.. figure:: /_images/code_examples/synth_flow/opt_02.*
   :class: width-helper

.. literalinclude:: /code_examples/synth_flow/opt_02.ys
   :language: yoscrypt
   :caption: ``docs/source/code_examples/synth_flow/opt_02.ys``

.. literalinclude:: /code_examples/synth_flow/opt_02.v
   :language: verilog
   :caption: ``docs/source/code_examples/synth_flow/opt_02.v``

.. figure:: /_images/code_examples/synth_flow/opt_03.*
   :class: width-helper

.. literalinclude:: /code_examples/synth_flow/opt_03.ys
   :language: yoscrypt
   :caption: ``docs/source/code_examples/synth_flow/opt_03.ys``

.. literalinclude:: /code_examples/synth_flow/opt_03.v
   :language: verilog
   :caption: ``docs/source/code_examples/synth_flow/opt_03.v``

.. figure:: /_images/code_examples/synth_flow/opt_04.*
   :class: width-helper

.. literalinclude:: /code_examples/synth_flow/opt_04.v
   :language: verilog
   :caption: ``docs/source/code_examples/synth_flow/opt_04.v``

.. literalinclude:: /code_examples/synth_flow/opt_04.ys
   :language: yoscrypt
   :caption: ``docs/source/code_examples/synth_flow/opt_04.ys``

When to use :cmd:ref:`opt` or :cmd:ref:`clean`
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Usually it does not hurt to call :cmd:ref:`opt` after each regular command in
the synthesis script. But it increases the synthesis time, so it is favourable
to only call :cmd:ref:`opt` when an improvement can be achieved.

It is generally a good idea to call :cmd:ref:`opt` before inherently expensive
commands such as :cmd:ref:`sat` or :cmd:ref:`freduce`, as the possible gain is
much higher in these cases as the possible loss.

The :cmd:ref:`clean` command on the other hand is very fast and many commands
leave a mess (dangling signal wires, etc). For example, most commands do not
remove any wires or cells. They just change the connections and depend on a
later call to clean to get rid of the now unused objects. So the occasional
``;;`` is a good idea in every synthesis script.

Other optimizations
-------------------

.. todo:: more on the other optimizations

- :doc:`/cmd/wreduce`
- :doc:`/cmd/peepopt`
- :doc:`/cmd/share`
- :cmd:ref:`abc` and :cmd:ref:`abc9`, see also: :doc:`abc`.
