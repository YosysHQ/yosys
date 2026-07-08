Coarse arithmetics
------------------

The `$fa` cell type represents a full adder. The cell is purely combinational
and bitwise.

.. code-block::

   X = A ^ B ^ C
   Y = (A & B) | (A & C) | (B & C)

.. table:: Ports

   ===== ======== =======
   Port  Dir      Width
   ===== ======== =======
   A     input    WIDTH
   B     input    WIDTH
   C     input    WIDTH
   X     output   WIDTH
   Y     output   WIDTH
   ===== ======== =======

.. table:: Parameters

   ========= ========= =================================
   Parameter Default   Description
   ========= ========= =================================
   WIDTH     1         Width of all ports
   ========= ========= =================================

The `$lcu` cell type is a lookahead carry unit. It computes carry bits in
parallel using propagate (P) and generate (G) signals, replacing the ripple
carry structure used in full-adder chains.

.. code-block::

   CO[0] = G[0] || (P[0] && CI)
   CO[i] = G[i] || (P[i] && CO[i-1])   (for i > 0)

.. table:: Ports

   ===== ======== ============== ===================================
   Port  Dir      Width          Description
   ===== ======== ============== ===================================
   P     input    WIDTH          Propagate signals
   G     input    WIDTH          Generate signals
   CI    input    1              Carry-in
   CO    output   WIDTH          Carry-out
   ===== ======== ============== ===================================

.. table:: Parameters

   ========= ========= =================================
   Parameter Default   Description
   ========= ========= =================================
   WIDTH     1         Width of P, G, and CO ports
   ========= ========= =================================

The `$lcu` cell is typically created during ``techmap`` of `$alu` cells. It has
multiple techmap implementations: Brent-Kung (default), Kogge-Stone, Sklansky,
and Han-Carlson.

The `$alu` cell type is an arithmetic logic unit supporting addition,
subtraction, and comparison operations. It is purely combinational.

The `$alu` cell computes:

.. code-block::

   Y = (A + B + CI)   when BI is 0
   Y = (A + ~B + CI)  when BI is 1

Comparison results are derived from the Y (sum), X (A xor B), CO (carry-out),
and CI (carry-in) signals.

.. table:: Ports

   ===== ======== =========== ==========================================
   Port  Dir      Width       Description
   ===== ======== =========== ==========================================
   A     input    A_WIDTH     Input operand
   B     input    B_WIDTH     Input operand
   CI    input    1           Carry-in (set for subtraction)
   BI    input    1           Invert-B (set for subtraction)
   X     output   Y_WIDTH     A xor B (sign-extended, optional B inversion)
   Y     output   Y_WIDTH     Sum
   CO    output   Y_WIDTH     Carry-out
   ===== ======== =========== ==========================================

.. table:: Parameters

   ========= ========= =================================
   Parameter Default   Description
   ========= ========= =================================
   A_SIGNED  0         Non-zero if A is signed
   B_SIGNED  0         Non-zero if B is signed
   A_WIDTH   1         Width of A port
   B_WIDTH   1         Width of B port
   Y_WIDTH   1         Width of X, Y, and CO ports
   ========= ========= =================================

The `$alu` cell is typically created by the ``alumacc`` pass by merging `$add`,
`$sub`, `$lt`, `$le`, `$ge`, `$gt`, `$eq`, `$ne`, and related cells into a
single arithmetic unit.

The `$macc` cell type represents a generalized multiply and accumulate
operation. The cell is purely combinational. It outputs the result of summing up
a sequence of products and other injected summands.

.. code-block::

   Y = 0 +- a0factor1 * a0factor2 +- a1factor1 * a1factor2 +- ...
        + B[0] + B[1] + ...

The A port consists of concatenated pairs of multiplier inputs ("factors"). A
zero length factor2 acts as a constant 1, turning factor1 into a simple summand.

In this pseudocode, ``u(foo)`` means an unsigned int that's foo bits long.

.. code-block::

   struct A {
      u(CONFIG.mul_info[0].factor1_len) a0factor1;
      u(CONFIG.mul_info[0].factor2_len) a0factor2;
      u(CONFIG.mul_info[1].factor1_len) a1factor1;
      u(CONFIG.mul_info[1].factor2_len) a1factor2;
      ...
   };

The cell's ``CONFIG`` parameter determines the layout of cell port ``A``. The
CONFIG parameter carries the following information:

.. code-block::

   struct CONFIG {
      u4 num_bits;
      struct mul_info {
         bool is_signed;
         bool is_subtract;
         u(num_bits) factor1_len;
         u(num_bits) factor2_len;
      }[num_ports];
   };

B is an array of concatenated 1-bit-wide unsigned integers to also be summed up.

.. note::

   The `$macc` cell type above is the original (legacy) version. The ``alumacc``
   pass now generates `$macc_v2` cells, which use separate ports ``A``, ``B``,
   ``C`` and explicit parameters (``NPRODUCTS``, ``NADDENDS``, ``A_WIDTHS``,
   ``B_WIDTHS``, ``C_WIDTHS``, ``A_SIGNED``, ``B_SIGNED``, ``C_SIGNED``,
   ``PRODUCT_NEGATED``, ``ADDEND_NEGATED``) instead of the packed A port and
   CONFIG parameter.

.. autocellgroup:: arith
   :members:
   :source:
   :linenos:
