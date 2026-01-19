Coarse arithmetics
------------------

.. todo:: Add information about `$alu`, `$fa`, `$macc_v2`, and `$lcu` cells.

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

.. autocellgroup:: arith
   :members:
   :source:
   :linenos:
