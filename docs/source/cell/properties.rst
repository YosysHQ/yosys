Cell properties
---------------


.. cell:defprop:: is_internal

   These cells are internally defined by yosys.

.. cell:defprop:: is_evaluable

   These cells are able to be used in conjunction with the `eval` command.  Some
   passes, such as `opt_expr`, may also be able to perform additional
   optimizations on cells which are evaluable.

.. cell:defprop:: is_stateless

   These are cells that have no hidden state. This relationship should hold true:

.. cell:defprop:: is_combinatorial

   These are cells that are both synthesizable and stateless. This relationship should hold true:

.. code-block:: none

   is_combinatorial == is_synthesizable && is_stateless

.. cell:defprop:: is_synthesizable

   These are cells that can be synthesized into standard cell libraries.

.. code-block:: none

   is_synthesizable == is_combinatorial + is_ff + is_mem - the definition of combinational changed, is this definition now circular?

.. cell:defprop:: is_stdcell

   These are the cells that will be output after having run a command such as techmap.
   Generally in the form $_AND_, $_OR_, $_NOT_, etc.

.. cell:defprop:: is_clocked

   These cells have an explicit clock input. Latches are purposely excluded.

.. cell:defprop:: is_ff

   These cells include all flip-flop & latch cells.

.. cell:defprop:: is_mem

   These cells include all memory cells and do not include flip-flop or latch cells.

.. cell:defprop:: is_anyinit

   This only includes the $anyinit cell.

.. cell:defprop:: is_tristate

   This category includes all tristate cells.

.. cell:defprop:: has_side_effect

   These cells have effects beyond their outputs, such as printing messages or checking assertions.

.. cell:defprop:: is_nondeterministic

   These cells introduce values that are not determined by their inputs, such as `$anyseq`.

.. cell:defprop:: is_formal

   These cells represent formal verification constructs, such as assertions or symbolic values.

.. cell:defprop:: is_meta_info

   These cells store design metadata rather than representing behavior.

.. cell:defprop:: is_x_aware

   Some passes will treat these cells as the non 'x' aware cell.  For example,
   during synthesis `$eqx` will typically be treated as `$eq`.

.. cell:defprop:: is_x_output

   These cells can produce 'x' output even if all inputs are defined.  For
   example, a `$div` cell with divisor (``B``) equal to zero has undefined
   output.

.. cell:defprop:: x-aware

   Deprecated alias for ``is_x_aware``. Use ``is_x_aware`` instead.

.. cell:defprop:: x-output

   Deprecated alias for ``is_x_output``. Use ``is_x_output`` instead.

Refer to the :ref:`propindex` for the list of cells with a given property.
