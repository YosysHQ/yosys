Wire cells
-------------------------

The `$slice` cell extracts a contiguous range of bits from its input. It
corresponds to a Verilog part-select expression.

.. code-block::

   Y = A[OFFSET +: Y_WIDTH]

.. table:: Ports

   ===== ======== =========== =====================================
   Port  Dir      Width       Description
   ===== ======== =========== =====================================
   A     input    A_WIDTH     Input signal
   Y     output   Y_WIDTH     Extracted bits
   ===== ======== =========== =====================================

.. table:: Parameters

   ========= ========= ==========================================
   Parameter Default   Description
   ========= ========= ==========================================
   A_WIDTH   0         Width of the input port A
   Y_WIDTH   0         Width of the output port Y
   OFFSET    0         Bit offset into A where the slice starts
   ========= ========= ==========================================

The `$concat` cell concatenates two inputs into a single output, with ``B``
occupying the most significant bits and ``A`` the least significant bits.

.. code-block::

   Y = {B, A}

.. table:: Ports

   ===== ======== ===================== =========================
   Port  Dir      Width                 Description
   ===== ======== ===================== =========================
   A     input    A_WIDTH               Lower bits of output
   B     input    B_WIDTH               Upper bits of output
   Y     output   A_WIDTH + B_WIDTH     Concatenated output
   ===== ======== ===================== =========================

.. table:: Parameters

   ========= ========= ============================
   Parameter Default   Description
   ========= ========= ============================
   A_WIDTH   0         Width of the input port A
   B_WIDTH   0         Width of the input port B
   ========= ========= ============================

.. autocellgroup:: wire
   :members:
   :source:
   :linenos:
