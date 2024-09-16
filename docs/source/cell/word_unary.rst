.. role:: verilog(code)
   :language: Verilog

Unary operators
---------------

All unary RTL cells have one input port ``A`` and one output port ``Y``. They
also have the following parameters:

``A_SIGNED``
   Set to a non-zero value if the input ``A`` is signed and therefore should be
   sign-extended when needed.

``A_WIDTH``
   The width of the input port ``A``.

``Y_WIDTH``
   The width of the output port ``Y``.

.. table:: Cell types for unary operators with their corresponding Verilog expressions.

   ================== ==============
   Verilog            Cell Type
   ================== ==============
   :verilog:`Y =  ~A` `$not`
   :verilog:`Y =  +A` `$pos`
   :verilog:`Y =  -A` `$neg`
   :verilog:`Y =  &A` `$reduce_and`
   :verilog:`Y =  |A` `$reduce_or`
   :verilog:`Y =  ^A` `$reduce_xor`
   :verilog:`Y = ~^A` `$reduce_xnor`
   :verilog:`Y =  |A` `$reduce_bool`
   :verilog:`Y =  !A` `$logic_not`
   ================== ==============

For the unary cells that output a logical value (`$reduce_and`, `$reduce_or`,
`$reduce_xor`, `$reduce_xnor`, `$reduce_bool`, `$logic_not`), when the
``Y_WIDTH`` parameter is greater than 1, the output is zero-extended, and only
the least significant bit varies.

Note that `$reduce_or` and `$reduce_bool` generally represent the same logic
function. But the `read_verilog` frontend will generate them in different
situations. A `$reduce_or` cell is generated when the prefix ``|`` operator is
being used. A `$reduce_bool` cell is generated when a bit vector is used as a
condition in an ``if``-statement or ``?:``-expression.

.. autocellgroup:: unary
   :members:
   :source:
   :linenos:
