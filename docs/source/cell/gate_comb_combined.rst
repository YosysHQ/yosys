.. role:: verilog(code)
   :language: Verilog

Combinatorial cells (combined)
------------------------------

These cells combine two or more combinatorial cells (simple) into a single cell.

.. table:: Cell types for gate level combinatorial cells (combined)

   ======================================= =============
   Verilog                                 Cell Type
   ======================================= =============
   :verilog:`Y = A & ~B`                   `$_ANDNOT_`
   :verilog:`Y = A | ~B`                   `$_ORNOT_`
   :verilog:`Y = ~((A & B) | C)`           `$_AOI3_`
   :verilog:`Y = ~((A | B) & C)`           `$_OAI3_`
   :verilog:`Y = ~((A & B) | (C & D))`     `$_AOI4_`
   :verilog:`Y = ~((A | B) & (C | D))`     `$_OAI4_`
   :verilog:`Y = ~(S ? B : A)`             `$_NMUX_`
   (see below)                             `$_MUX4_`
   (see below)                             `$_MUX8_`
   (see below)                             `$_MUX16_`
   ======================================= =============

The `$_MUX4_`, `$_MUX8_` and `$_MUX16_` cells are used to model wide muxes, and
correspond to the following Verilog code:

.. code-block:: verilog
   :force:

   // $_MUX4_
   assign Y = T ? (S ? D : C) :
                  (S ? B : A);
   // $_MUX8_
   assign Y = U ? T ? (S ? H : G) :
                      (S ? F : E) :
                  T ? (S ? D : C) :
                      (S ? B : A);
   // $_MUX16_
   assign Y = V ? U ? T ? (S ? P : O) :
                          (S ? N : M) :
                      T ? (S ? L : K) :
                          (S ? J : I) :
                  U ? T ? (S ? H : G) :
                          (S ? F : E) :
                      T ? (S ? D : C) :
                          (S ? B : A);

.. autocellgroup:: comb_combined
   :members:
   :source:
   :linenos:
