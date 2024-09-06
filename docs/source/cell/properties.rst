Cell properties
---------------

.. TODO:: Fill :cell:ref:`is_evaluable`

.. cell:defprop:: is_evaluable

.. cell:defprop:: x-aware

   Some passes will treat these cells as the non 'x' aware cell.  For example,
   during synthesis `$eqx` will typically be treated as `$eq`.

.. cell:defprop:: x-output

   These cells can produce 'x' output even if all inputs are defined.  For
   example, a `$div` cell with ``B=0`` has undefined output.

Refer to the :ref:`propindex` for the list of cells with a given property.
