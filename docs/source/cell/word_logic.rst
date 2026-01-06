Arbitrary logic functions
-------------------------

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

.. autocellgroup:: logic
   :members:
   :source:
   :linenos: