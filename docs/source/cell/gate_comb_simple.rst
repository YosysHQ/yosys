.. role:: verilog(code)
   :language: Verilog

Combinatorial cells (simple)
----------------------------

.. table:: Cell types for gate level combinatorial cells (simple)

   ======================================= =============
   Verilog                                 Cell Type
   ======================================= =============
   :verilog:`Y = A`                        `$_BUF_`
   :verilog:`Y = ~A`                       `$_NOT_`
   :verilog:`Y = A & B`                    `$_AND_`
   :verilog:`Y = ~(A & B)`                 `$_NAND_`
   :verilog:`Y = A | B`                    `$_OR_`
   :verilog:`Y = ~(A | B)`                 `$_NOR_`
   :verilog:`Y = A ^ B`                    `$_XOR_`
   :verilog:`Y = ~(A ^ B)`                 `$_XNOR_`
   :verilog:`Y = S ? B : A`                `$_MUX_`
   ======================================= =============

.. autocellgroup:: comb_simple
   :members:
   :source:
   :linenos:
