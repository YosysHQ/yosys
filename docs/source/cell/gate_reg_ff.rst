.. role:: verilog(code)
   :language: Verilog

Flip-flop cells
---------------

The cell types `$_DFF_N_` and `$_DFF_P_` represent d-type flip-flops.

.. table:: Cell types for basic flip-flops

   ======================================= =============
   Verilog                                 Cell Type
   ======================================= =============
   :verilog:`always @(negedge C) Q <= D`   `$_DFF_N_`
   :verilog:`always @(posedge C) Q <= D`   `$_DFF_P_`
   ======================================= =============

The cell types ``$_DFFE_[NP][NP]_`` implement d-type flip-flops with enable. The
values in the table for these cell types relate to the following Verilog code
template.

.. code-block:: verilog
   :force:

   always @(CLK_EDGE C)
      if (EN == EN_LVL)
         Q <= D;


.. table:: Cell types for gate level logic networks (FFs with enable)
   :name: tab:CellLib_gates_dffe

   ================== ============= ============
   :math:`ClkEdge`    :math:`EnLvl` Cell Type
   ================== ============= ============
   :verilog:`negedge` ``0``         `$_DFFE_NN_`
   :verilog:`negedge` ``1``         `$_DFFE_NP_`
   :verilog:`posedge` ``0``         `$_DFFE_PN_`
   :verilog:`posedge` ``1``         `$_DFFE_PP_`
   ================== ============= ============

The cell types ``$_DFF_[NP][NP][01]_`` implement d-type flip-flops with
asynchronous reset. The values in the table for these cell types relate to the
following Verilog code template, where ``RST_EDGE`` is ``posedge`` if
``RST_LVL`` if ``1``, and ``negedge`` otherwise.

.. code-block:: verilog
   :force:

   always @(CLK_EDGE C, RST_EDGE R)
      if (R == RST_LVL)
         Q <= RST_VAL;
      else
         Q <= D;

The cell types ``$_SDFF_[NP][NP][01]_`` implement d-type flip-flops with
synchronous reset. The values in the table for these cell types relate to the
following Verilog code template:

.. code-block:: verilog
   :force:

   always @(CLK_EDGE C)
      if (R == RST_LVL)
         Q <= RST_VAL;
      else
         Q <= D;

.. table:: Cell types for gate level logic networks (FFs with reset)
   :name: tab:CellLib_gates_adff

   ================== ============== ============== ===========================
   :math:`ClkEdge`    :math:`RstLvl` :math:`RstVal` Cell Type
   ================== ============== ============== ===========================
   :verilog:`negedge` ``0``          ``0``          `$_DFF_NN0_`, `$_SDFF_NN0_`
   :verilog:`negedge` ``0``          ``1``          `$_DFF_NN1_`, `$_SDFF_NN1_`
   :verilog:`negedge` ``1``          ``0``          `$_DFF_NP0_`, `$_SDFF_NP0_`
   :verilog:`negedge` ``1``          ``1``          `$_DFF_NP1_`, `$_SDFF_NP1_`
   :verilog:`posedge` ``0``          ``0``          `$_DFF_PN0_`, `$_SDFF_PN0_`
   :verilog:`posedge` ``0``          ``1``          `$_DFF_PN1_`, `$_SDFF_PN1_`
   :verilog:`posedge` ``1``          ``0``          `$_DFF_PP0_`, `$_SDFF_PP0_`
   :verilog:`posedge` ``1``          ``1``          `$_DFF_PP1_`, `$_SDFF_PP1_`
   ================== ============== ============== ===========================

The cell types ``$_DFFE_[NP][NP][01][NP]_`` implement d-type flip-flops with
asynchronous reset and enable. The values in the table for these cell types
relate to the following Verilog code template, where ``RST_EDGE`` is ``posedge``
if ``RST_LVL`` if ``1``, and ``negedge`` otherwise.

.. code-block:: verilog
   :force:

   always @(CLK_EDGE C, RST_EDGE R)
      if (R == RST_LVL)
         Q <= RST_VAL;
      else if (EN == EN_LVL)
         Q <= D;

The cell types ``$_SDFFE_[NP][NP][01][NP]_`` implement d-type flip-flops with
synchronous reset and enable, with reset having priority over enable. The values
in the table for these cell types relate to the following Verilog code template:

.. code-block:: verilog
   :force:

   always @(CLK_EDGE C)
      if (R == RST_LVL)
         Q <= RST_VAL;
      else if (EN == EN_LVL)
         Q <= D;

The cell types ``$_SDFFCE_[NP][NP][01][NP]_`` implement d-type flip-flops with
synchronous reset and enable, with enable having priority over reset. The values
in the table for these cell types relate to the following Verilog code template:

.. code-block:: verilog
   :force:

   always @(CLK_EDGE C)
      if (EN == EN_LVL)
         if (R == RST_LVL)
            Q <= RST_VAL;
         else
            Q <= D;


.. table:: Cell types for gate level logic networks (FFs with reset and enable)
   :name: tab:CellLib_gates_adffe

   ================== ============== ============== ============= =================================================
   :math:`ClkEdge`    :math:`RstLvl` :math:`RstVal` :math:`EnLvl` Cell Type
   ================== ============== ============== ============= =================================================
   :verilog:`negedge` ``0``          ``0``          ``0``         `$_DFFE_NN0N_`, `$_SDFFE_NN0N_`, `$_SDFFCE_NN0N_`
   :verilog:`negedge` ``0``          ``0``          ``1``         `$_DFFE_NN0P_`, `$_SDFFE_NN0P_`, `$_SDFFCE_NN0P_`
   :verilog:`negedge` ``0``          ``1``          ``0``         `$_DFFE_NN1N_`, `$_SDFFE_NN1N_`, `$_SDFFCE_NN1N_`
   :verilog:`negedge` ``0``          ``1``          ``1``         `$_DFFE_NN1P_`, `$_SDFFE_NN1P_`, `$_SDFFCE_NN1P_`
   :verilog:`negedge` ``1``          ``0``          ``0``         `$_DFFE_NP0N_`, `$_SDFFE_NP0N_`, `$_SDFFCE_NP0N_`
   :verilog:`negedge` ``1``          ``0``          ``1``         `$_DFFE_NP0P_`, `$_SDFFE_NP0P_`, `$_SDFFCE_NP0P_`
   :verilog:`negedge` ``1``          ``1``          ``0``         `$_DFFE_NP1N_`, `$_SDFFE_NP1N_`, `$_SDFFCE_NP1N_`
   :verilog:`negedge` ``1``          ``1``          ``1``         `$_DFFE_NP1P_`, `$_SDFFE_NP1P_`, `$_SDFFCE_NP1P_`
   :verilog:`posedge` ``0``          ``0``          ``0``         `$_DFFE_PN0N_`, `$_SDFFE_PN0N_`, `$_SDFFCE_PN0N_`
   :verilog:`posedge` ``0``          ``0``          ``1``         `$_DFFE_PN0P_`, `$_SDFFE_PN0P_`, `$_SDFFCE_PN0P_`
   :verilog:`posedge` ``0``          ``1``          ``0``         `$_DFFE_PN1N_`, `$_SDFFE_PN1N_`, `$_SDFFCE_PN1N_`
   :verilog:`posedge` ``0``          ``1``          ``1``         `$_DFFE_PN1P_`, `$_SDFFE_PN1P_`, `$_SDFFCE_PN1P_`
   :verilog:`posedge` ``1``          ``0``          ``0``         `$_DFFE_PP0N_`, `$_SDFFE_PP0N_`, `$_SDFFCE_PP0N_`
   :verilog:`posedge` ``1``          ``0``          ``1``         `$_DFFE_PP0P_`, `$_SDFFE_PP0P_`, `$_SDFFCE_PP0P_`
   :verilog:`posedge` ``1``          ``1``          ``0``         `$_DFFE_PP1N_`, `$_SDFFE_PP1N_`, `$_SDFFCE_PP1N_`
   :verilog:`posedge` ``1``          ``1``          ``1``         `$_DFFE_PP1P_`, `$_SDFFE_PP1P_`, `$_SDFFCE_PP1P_`
   ================== ============== ============== ============= =================================================

The cell types ``$_DFFSR_[NP][NP][NP]_`` implement d-type flip-flops with
asynchronous set and reset. The values in the table for these cell types relate
to the following Verilog code template, where ``RST_EDGE`` is ``posedge`` if
``RST_LVL`` if ``1``, ``negedge`` otherwise, and ``SET_EDGE`` is ``posedge`` if
``SET_LVL`` if ``1``, ``negedge`` otherwise.

.. code-block:: verilog
   :force:

   always @(CLK_EDGE C, RST_EDGE R, SET_EDGE S)
      if (R == RST_LVL)
         Q <= 0;
      else if (S == SET_LVL)
         Q <= 1;
      else
         Q <= D;

.. table:: Cell types for gate level logic networks (FFs with set and reset)
   :name: tab:CellLib_gates_dffsr

   ================== ============== ============== ==============
   :math:`ClkEdge`    :math:`SetLvl` :math:`RstLvl` Cell Type
   ================== ============== ============== ==============
   :verilog:`negedge` ``0``          ``0``          `$_DFFSR_NNN_`
   :verilog:`negedge` ``0``          ``1``          `$_DFFSR_NNP_`
   :verilog:`negedge` ``1``          ``0``          `$_DFFSR_NPN_`
   :verilog:`negedge` ``1``          ``1``          `$_DFFSR_NPP_`
   :verilog:`posedge` ``0``          ``0``          `$_DFFSR_PNN_`
   :verilog:`posedge` ``0``          ``1``          `$_DFFSR_PNP_`
   :verilog:`posedge` ``1``          ``0``          `$_DFFSR_PPN_`
   :verilog:`posedge` ``1``          ``1``          `$_DFFSR_PPP_`
   ================== ============== ============== ==============

The cell types ``$_DFFSRE_[NP][NP][NP][NP]_`` implement d-type flip-flops with
asynchronous set and reset and enable. The values in the table for these cell
types relate to the following Verilog code template, where ``RST_EDGE`` is
``posedge`` if ``RST_LVL`` if ``1``, ``negedge`` otherwise, and ``SET_EDGE`` is
``posedge`` if ``SET_LVL`` if ``1``, ``negedge`` otherwise.

.. code-block:: verilog
   :force:

   always @(CLK_EDGE C, RST_EDGE R, SET_EDGE S)
      if (R == RST_LVL)
         Q <= 0;
      else if (S == SET_LVL)
         Q <= 1;
      else if (E == EN_LVL)
         Q <= D;


.. table:: Cell types for gate level logic networks (FFs with set and reset and enable)
   :name: tab:CellLib_gates_dffsre

   ================== ============== ============== ============= ================
   :math:`ClkEdge`    :math:`SetLvl` :math:`RstLvl` :math:`EnLvl` Cell Type
   ================== ============== ============== ============= ================
   :verilog:`negedge` ``0``          ``0``          ``0``         `$_DFFSRE_NNNN_`
   :verilog:`negedge` ``0``          ``0``          ``1``         `$_DFFSRE_NNNP_`
   :verilog:`negedge` ``0``          ``1``          ``0``         `$_DFFSRE_NNPN_`
   :verilog:`negedge` ``0``          ``1``          ``1``         `$_DFFSRE_NNPP_`
   :verilog:`negedge` ``1``          ``0``          ``0``         `$_DFFSRE_NPNN_`
   :verilog:`negedge` ``1``          ``0``          ``1``         `$_DFFSRE_NPNP_`
   :verilog:`negedge` ``1``          ``1``          ``0``         `$_DFFSRE_NPPN_`
   :verilog:`negedge` ``1``          ``1``          ``1``         `$_DFFSRE_NPPP_`
   :verilog:`posedge` ``0``          ``0``          ``0``         `$_DFFSRE_PNNN_`
   :verilog:`posedge` ``0``          ``0``          ``1``         `$_DFFSRE_PNNP_`
   :verilog:`posedge` ``0``          ``1``          ``0``         `$_DFFSRE_PNPN_`
   :verilog:`posedge` ``0``          ``1``          ``1``         `$_DFFSRE_PNPP_`
   :verilog:`posedge` ``1``          ``0``          ``0``         `$_DFFSRE_PPNN_`
   :verilog:`posedge` ``1``          ``0``          ``1``         `$_DFFSRE_PPNP_`
   :verilog:`posedge` ``1``          ``1``          ``0``         `$_DFFSRE_PPPN_`
   :verilog:`posedge` ``1``          ``1``          ``1``         `$_DFFSRE_PPPP_`
   ================== ============== ============== ============= ================

.. todo:: flip-flops with async load, ``$_ALDFFE?_[NP]{2,3}_``

.. autocellgroup:: reg_ff
   :members:
   :source:
   :linenos:
