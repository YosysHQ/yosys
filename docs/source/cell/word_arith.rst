Coarse arithmetics
------------------

Multiply-accumulate
~~~~~~~~~~~~~~~~~~~

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

Arbitrary logic functions
~~~~~~~~~~~~~~~~~~~~~~~~~

The `$lut` cell type implements a single-output LUT (lookup table). It
implements an arbitrary logic function with its ``\LUT`` parameter to map input
port ``\A`` to values of ``\Y`` output port values. In psuedocode: ``Y =
\LUT[A]``. ``\A`` has width set by parameter ``\WIDTH`` and ``\Y`` has a width
of 1. Every logic function with a single bit output has a unique `$lut`
representation.

The `$sop` cell type implements a sum-of-products expression, also known as
disjunctive normal form (DNF). It implements an arbitrary logic function. Its
structure mimics a programmable logic array (PLA). Output port ``\Y`` is the sum
of products of the bits of the input port ``\A`` as defined by parameter
``\TABLE``. ``\A`` is ``\WIDTH`` bits wide. The number of products in the sum is
set by parameter ``\DEPTH``, and each product has two bits for each input bit -
for the presence of the unnegated and negated version of said input bit in the
product. Therefore the ``\TABLE`` parameter holds ``2 * \WIDTH * \DEPTH`` bits.

For example:

Let ``\WIDTH`` be 3. We would like to represent ``\Y =~\A[0] + \A[1]~\A[2]``.
There are 2 products to be summed, so ``\DEPTH`` shall be 2.

.. code-block::

    ~A[2]-----+
     A[2]----+|
    ~A[1]---+||
     A[1]--+|||
    ~A[0]-+||||
     A[0]+||||| 
         |||||| product formula
         010000 ~\A[0]
         001001 \A[1]~\A[2]

So the value of ``\TABLE`` will become ``010000001001``.

Any logic function with a single bit output can be represented with ``$sop`` but
may have variously minimized or ordered summands represented in the ``\TABLE``
values.

.. autocellgroup:: arith
   :members:
   :source:
   :linenos:
