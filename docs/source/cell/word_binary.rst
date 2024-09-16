.. role:: verilog(code)
   :language: Verilog

Binary operators
~~~~~~~~~~~~~~~~

All binary RTL cells have two input ports ``A`` and ``B`` and one output port
``Y``. They also have the following parameters:

``A_SIGNED``
   Set to a non-zero value if the input ``A`` is signed and therefore should be
   sign-extended when needed.

``A_WIDTH``
   The width of the input port ``A``.

``B_SIGNED``
   Set to a non-zero value if the input ``B`` is signed and therefore should be
   sign-extended when needed.

``B_WIDTH``
   The width of the input port ``B``.

``Y_WIDTH``
   The width of the output port ``Y``.

.. table:: Cell types for binary operators with their corresponding Verilog expressions.

   ======================= =============== ======================= ===========
   Verilog                 Cell Type       Verilog                 Cell Type
   ======================= =============== ======================= ===========
   :verilog:`Y = A  & B`   `$and`          :verilog:`Y = A ** B`   `$pow`
   :verilog:`Y = A  | B`   `$or`           :verilog:`Y = A <  B`   `$lt`
   :verilog:`Y = A  ^ B`   `$xor`          :verilog:`Y = A <= B`   `$le`
   :verilog:`Y = A ~^ B`   `$xnor`         :verilog:`Y = A == B`   `$eq`
   :verilog:`Y = A << B`   `$shl`          :verilog:`Y = A != B`   `$ne`
   :verilog:`Y = A >> B`   `$shr`          :verilog:`Y = A >= B`   `$ge`
   :verilog:`Y = A <<< B`  `$sshl`         :verilog:`Y = A >  B`   `$gt`
   :verilog:`Y = A >>> B`  `$sshr`         :verilog:`Y = A  + B`   `$add`
   :verilog:`Y = A && B`   `$logic_and`    :verilog:`Y = A  - B`   `$sub`
   :verilog:`Y = A || B`   `$logic_or`     :verilog:`Y = A  * B`   `$mul`
   :verilog:`Y = A === B`  `$eqx`          :verilog:`Y = A  / B`   `$div`
   :verilog:`Y = A !== B`  `$nex`          :verilog:`Y = A  % B`   `$mod`
   ``N/A``                 `$shift`        ``N/A``                 `$divfloor`
   ``N/A``                 `$shiftx`       ``N/A``                 `$modfloor`
   ======================= =============== ======================= ===========

The `$shl` and `$shr` cells implement logical shifts, whereas the `$sshl` and
`$sshr` cells implement arithmetic shifts. The `$shl` and `$sshl` cells
implement the same operation. All four of these cells interpret the second
operand as unsigned, and require ``B_SIGNED`` to be zero.

Two additional shift operator cells are available that do not directly
correspond to any operator in Verilog, `$shift` and `$shiftx`. The `$shift` cell
performs a right logical shift if the second operand is positive (or unsigned),
and a left logical shift if it is negative. The `$shiftx` cell performs the same
operation as the `$shift` cell, but the vacated bit positions are filled with
undef (x) bits, and corresponds to the Verilog indexed part-select expression.

For the binary cells that output a logical value (`$logic_and`, `$logic_or`,
`$eqx`, `$nex`, `$lt`, `$le`, `$eq`, `$ne`, `$ge`, `$gt`), when the ``Y_WIDTH``
parameter is greater than 1, the output is zero-extended, and only the least
significant bit varies.

Division and modulo cells are available in two rounding modes. The original
`$div` and `$mod` cells are based on truncating division, and correspond to the
semantics of the verilog ``/`` and ``%`` operators. The `$divfloor` and
`$modfloor` cells represent flooring division and flooring modulo, the latter of
which corresponds to the ``%`` operator in Python. See the following table for a
side-by-side comparison between the different semantics.

.. table:: Comparison between different rounding modes for division and modulo cells.

   +-----------+--------+-----------+-----------+-----------+-----------+
   | Division  | Result |      Truncating       |        Flooring       |
   +-----------+--------+-----------+-----------+-----------+-----------+
   |           |        | $div      | $mod      | $divfloor | $modfloor |
   +===========+========+===========+===========+===========+===========+
   | -10 / 3   | -3.3   | -3        |        -1 | -4        |  2        |
   +-----------+--------+-----------+-----------+-----------+-----------+
   | 10 / -3   | -3.3   | -3        |         1 | -4        | -2        |
   +-----------+--------+-----------+-----------+-----------+-----------+
   | -10 / -3  |  3.3   |  3        |        -1 |  3        | -1        |
   +-----------+--------+-----------+-----------+-----------+-----------+
   | 10 / 3    |  3.3   |  3        |         1 |  3        |  1        |
   +-----------+--------+-----------+-----------+-----------+-----------+

.. autocellgroup:: binary
   :members:
   :source:
   :linenos:
