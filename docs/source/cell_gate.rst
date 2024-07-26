.. role:: verilog(code)
   :language: Verilog

.. _sec:celllib_gates:

Gate-level cells
----------------

.. todo:: Split gate-level cells into subpages

   Consider also checking wording to be less academic and consistent.

For gate level logic networks, fixed function single bit cells are used that do
not provide any parameters.

Simulation models for these cells can be found in the file
techlibs/common/simcells.v in the Yosys source tree.

.. table:: Cell types for gate level logic networks (main list)
   :name: tab:CellLib_gates

   ======================================= =============
   Verilog                                 Cell Type
   ======================================= =============
   :verilog:`Y = A`                        `$_BUF_`
   :verilog:`Y = ~A`                       `$_NOT_`
   :verilog:`Y = A & B`                    `$_AND_`
   :verilog:`Y = ~(A & B)`                 `$_NAND_`
   :verilog:`Y = A & ~B`                   `$_ANDNOT_`
   :verilog:`Y = A | B`                    `$_OR_`
   :verilog:`Y = ~(A | B)`                 `$_NOR_`
   :verilog:`Y = A | ~B`                   `$_ORNOT_`
   :verilog:`Y = A ^ B`                    `$_XOR_`
   :verilog:`Y = ~(A ^ B)`                 `$_XNOR_`
   :verilog:`Y = ~((A & B) | C)`           `$_AOI3_`
   :verilog:`Y = ~((A | B) & C)`           `$_OAI3_`
   :verilog:`Y = ~((A & B) | (C & D))`     `$_AOI4_`
   :verilog:`Y = ~((A | B) & (C | D))`     `$_OAI4_`
   :verilog:`Y = S ? B : A`                `$_MUX_`
   :verilog:`Y = ~(S ? B : A)`             `$_NMUX_`
   (see below)                             `$_MUX4_`
   (see below)                             `$_MUX8_`
   (see below)                             `$_MUX16_`
   :verilog:`Y = EN ? A : 1'bz`            `$_TBUF_`
   :verilog:`always @(negedge C) Q <= D`   `$_DFF_N_`
   :verilog:`always @(posedge C) Q <= D`   `$_DFF_P_`
   :verilog:`always @* if (!E) Q <= D`     `$_DLATCH_N_`
   :verilog:`always @* if (E)  Q <= D`     `$_DLATCH_P_`
   ======================================= =============

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


Tables :numref:`%s <tab:CellLib_gates>`, :numref:`%s <tab:CellLib_gates_dffe>`,
:numref:`%s <tab:CellLib_gates_adff>`, :numref:`%s <tab:CellLib_gates_adffe>`,
:numref:`%s <tab:CellLib_gates_dffsr>`, :numref:`%s <tab:CellLib_gates_dffsre>`,
:numref:`%s <tab:CellLib_gates_adlatch>`, :numref:`%s
<tab:CellLib_gates_dlatchsr>` and :numref:`%s <tab:CellLib_gates_sr>` list all
cell types used for gate level logic. The cell types `$_BUF_`, `$_NOT_`,
`$_AND_`, `$_NAND_`, `$_ANDNOT_`, `$_OR_`, `$_NOR_`, `$_ORNOT_`, `$_XOR_`,
`$_XNOR_`, `$_AOI3_`, `$_OAI3_`, `$_AOI4_`, `$_OAI4_`, `$_MUX_`, `$_MUX4_`,
`$_MUX8_`, `$_MUX16_` and `$_NMUX_` are used to model combinatorial logic. The
cell type `$_TBUF_` is used to model tristate logic.

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

The cell types `$_DFF_N_` and `$_DFF_P_` represent d-type flip-flops.

The cell types ``$_DFFE_[NP][NP]_`` implement d-type flip-flops with enable. The
values in the table for these cell types relate to the following Verilog code
template.

.. code-block:: verilog
   :force:

   always @(CLK_EDGE C)
      if (EN == EN_LVL)
         Q <= D;

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

The cell types `$_DLATCH_N_` and `$_DLATCH_P_` represent d-type latches.

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

The cell types ``$_SR_[NP][NP]_`` implement sr-type latches. The values in the
table for these cell types relate to the following Verilog code template:

.. code-block:: verilog
   :force:

   always @*
      if (R == RST_LVL)
         Q <= 0;
      else if (S == SET_LVL)
         Q <= 1;

In most cases gate level logic networks are created from RTL networks using the
techmap pass. The flip-flop cells from the gate level logic network can be
mapped to physical flip-flop cells from a Liberty file using the dfflibmap pass.
The combinatorial logic cells can be mapped to physical cells from a Liberty
file via ABC using the abc pass.

.. toctree::
   :caption: Gate-level cells
   :maxdepth: 2

   /cell/gate_other
