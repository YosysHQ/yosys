.. role:: verilog(code)
   :language: Verilog

Latch cells
-----------

The cell types `$_DLATCH_N_` and `$_DLATCH_P_` represent d-type latches.

.. table:: Cell types for basic latches

   ======================================= =============
   Verilog                                 Cell Type
   ======================================= =============
   :verilog:`always @* if (!E) Q <= D`     `$_DLATCH_N_`
   :verilog:`always @* if (E)  Q <= D`     `$_DLATCH_P_`
   ======================================= =============

The cell types ``$_DLATCH_[NP][NP][01]_`` implement d-type latches with reset.
The values in the table for these cell types relate to the following Verilog
code template:

.. code-block:: verilog
   :force:

   always @*
      if (R == RST_LVL)
         Q <= RST_VAL;
      else if (E == EN_LVL)
         Q <= D;

.. table:: Cell types for gate level logic networks (latches with reset)
   :name: tab:CellLib_gates_adlatch

   ============= ============== ============== ===============
   :math:`EnLvl` :math:`RstLvl` :math:`RstVal` Cell Type
   ============= ============== ============== ===============
   ``0``         ``0``          ``0``          `$_DLATCH_NN0_`
   ``0``         ``0``          ``1``          `$_DLATCH_NN1_`
   ``0``         ``1``          ``0``          `$_DLATCH_NP0_`
   ``0``         ``1``          ``1``          `$_DLATCH_NP1_`
   ``1``         ``0``          ``0``          `$_DLATCH_PN0_`
   ``1``         ``0``          ``1``          `$_DLATCH_PN1_`
   ``1``         ``1``          ``0``          `$_DLATCH_PP0_`
   ``1``         ``1``          ``1``          `$_DLATCH_PP1_`
   ============= ============== ============== ===============

The cell types ``$_DLATCHSR_[NP][NP][NP]_`` implement d-type latches with set
and reset. The values in the table for these cell types relate to the following
Verilog code template:

.. code-block:: verilog
   :force:

   always @*
      if (R == RST_LVL)
         Q <= 0;
      else if (S == SET_LVL)
         Q <= 1;
      else if (E == EN_LVL)
         Q <= D;

.. table:: Cell types for gate level logic networks (latches with set and reset)
   :name: tab:CellLib_gates_dlatchsr

   ============= ============== ============== =================
   :math:`EnLvl` :math:`SetLvl` :math:`RstLvl` Cell Type
   ============= ============== ============== =================
   ``0``         ``0``          ``0``          `$_DLATCHSR_NNN_`
   ``0``         ``0``          ``1``          `$_DLATCHSR_NNP_`
   ``0``         ``1``          ``0``          `$_DLATCHSR_NPN_`
   ``0``         ``1``          ``1``          `$_DLATCHSR_NPP_`
   ``1``         ``0``          ``0``          `$_DLATCHSR_PNN_`
   ``1``         ``0``          ``1``          `$_DLATCHSR_PNP_`
   ``1``         ``1``          ``0``          `$_DLATCHSR_PPN_`
   ``1``         ``1``          ``1``          `$_DLATCHSR_PPP_`
   ============= ============== ============== =================

The cell types ``$_SR_[NP][NP]_`` implement sr-type latches. The values in the
table for these cell types relate to the following Verilog code template:

.. code-block:: verilog
   :force:

   always @*
      if (R == RST_LVL)
         Q <= 0;
      else if (S == SET_LVL)
         Q <= 1;

.. table:: Cell types for gate level logic networks (SR latches)
   :name: tab:CellLib_gates_sr

   ============== ============== ==========
   :math:`SetLvl` :math:`RstLvl` Cell Type
   ============== ============== ==========
   ``0``          ``0``          `$_SR_NN_`
   ``0``          ``1``          `$_SR_NP_`
   ``1``          ``0``          `$_SR_PN_`
   ``1``          ``1``          `$_SR_PP_`
   ============== ============== ==========

.. autocellgroup:: reg_latch
   :members:
   :source:
   :linenos:
