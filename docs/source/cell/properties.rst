Cell properties
---------------

.. cell:defprop:: is_evaluable

   These cells are able to be used in conjunction with the `eval` command.  Some
   passes, such as `opt_expr`, may also be able to perform additional
   optimizations on cells which are evaluable.

.. cell:defprop:: x-aware

   Some passes will treat these cells as the non 'x' aware cell.  For example,
   during synthesis `$eqx` will typically be treated as `$eq`.

.. cell:defprop:: x-output

   These cells can produce 'x' output even if all inputs are defined.  For
   example, a `$div` cell with divisor (``B``) equal to zero has undefined
   output.

Refer to the :ref:`propindex` for the list of cells with a given property.
