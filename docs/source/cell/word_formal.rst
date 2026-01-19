Formal verification cells
-------------------------

.. role:: yoscrypt(code)
   :language: yoscrypt

.. note::

   Some front-ends may not support the generic `$check` cell, in such cases
   calling :yoscrypt:`chformal -lower` will convert each `$check` cell into it's
   equivalent.  See `chformal` for more.

.. todo:: Describe formal cells

   `$check`, `$assert`, `$assume`, `$live`, `$fair`, `$cover`, `$equiv`,
   `$initstate`, `$anyconst`, `$anyseq`, `$anyinit`, `$allconst`, and `$allseq`.

   Also `$ff` and `$_FF_` cells.

.. autocellgroup:: formal
   :members:
   :source:
   :linenos:

Formal support cells
~~~~~~~~~~~~~~~~~~~~

.. autocellgroup:: formal_tag
   :members:
   :source:
   :linenos:
