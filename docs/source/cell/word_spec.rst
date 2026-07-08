Specify rules
-------------

Specify cells encode Verilog ``specify`` block timing constraints and checks.
They are created when elaborating ``specify`` blocks and consumed by timing
analysis tools.

The `$specify2` cell represents a simple combinational path delay between a
source port and a destination port (without edge sensitivity on the source).

.. table:: Ports

   ===== ======== ============== ================================
   Port  Dir      Width          Description
   ===== ======== ============== ================================
   EN    input    1              Enable (condition guard)
   SRC   input    SRC_WIDTH      Source signal(s)
   DST   input    DST_WIDTH      Destination signal(s)
   ===== ======== ============== ================================

.. table:: Parameters

   ============= ================================================================
   Parameter     Description
   ============= ================================================================
   FULL          0: simple path (``=>``) — each SRC bit to matching DST bit;
                 1: full cross path (``*>``) — every SRC bit to every DST bit
   SRC_WIDTH     Width of SRC port
   DST_WIDTH     Width of DST port
   SRC_DST_PEN   Source polarity filter enabled
   SRC_DST_POL   Source polarity filter level (when SRC_DST_PEN is set)
   T_RISE_MIN    Rise delay minimum (in simulator time units)
   T_RISE_TYP    Rise delay typical
   T_RISE_MAX    Rise delay maximum
   T_FALL_MIN    Fall delay minimum
   T_FALL_TYP    Fall delay typical
   T_FALL_MAX    Fall delay maximum
   ============= ================================================================

The `$specify3` cell represents a registered (edge-sensitive) path delay, as in
``(posedge CLK => (Q : D))``. It adds an edge condition on the source and an
optional data signal.

.. table:: Ports

   ===== ======== ============== =============================================
   Port  Dir      Width          Description
   ===== ======== ============== =============================================
   EN    input    1              Enable (condition guard)
   SRC   input    SRC_WIDTH      Clock/source signal(s)
   DST   input    DST_WIDTH      Destination signal(s)
   DAT   input    DST_WIDTH      Data signal(s) for the path (``Q : D`` form)
   ===== ======== ============== =============================================

.. table:: Parameters

   ============= ================================================================
   Parameter     Description
   ============= ================================================================
   FULL          0: simple path (``=>``); 1: full cross path (``*>``)
   SRC_WIDTH     Width of SRC port
   DST_WIDTH     Width of DST, DAT ports
   EDGE_EN       Source edge sensitivity enabled
   EDGE_POL      Source edge polarity: 1 for posedge, 0 for negedge
   SRC_DST_PEN   Source-to-destination polarity filter enabled
   SRC_DST_POL   Source-to-destination polarity filter level
   DAT_DST_PEN   Data-to-destination polarity filter enabled
   DAT_DST_POL   Data-to-destination polarity filter level
   T_RISE_MIN    Rise delay minimum
   T_RISE_TYP    Rise delay typical
   T_RISE_MAX    Rise delay maximum
   T_FALL_MIN    Fall delay minimum
   T_FALL_TYP    Fall delay typical
   T_FALL_MAX    Fall delay maximum
   ============= ================================================================

The `$specrule` cell represents a timing check rule from a Verilog ``specify``
block (e.g. ``$setup``, ``$hold``, ``$setuphold``).

.. table:: Ports

   ======== ======== ============== =========================================
   Port     Dir      Width          Description
   ======== ======== ============== =========================================
   SRC_EN   input    1              Enable for the source signal
   DST_EN   input    1              Enable for the destination signal
   SRC      input    SRC_WIDTH      Source (reference) signal
   DST      input    DST_WIDTH      Destination (constrained) signal
   ======== ======== ============== =========================================

.. table:: Parameters

   ========== ====================================================================
   Parameter  Description
   ========== ====================================================================
   TYPE       Type of timing check: ``"$setup"``, ``"$hold"``, ``"$setuphold"``,
              ``"$removal"``, ``"$recovery"``, ``"$recrem"``, ``"$skew"``,
              ``"$timeskew"``, ``"$fullskew"``, ``"$nochange"``
   T_LIMIT    Primary timing limit
   T_LIMIT2   Secondary timing limit (used by ``$setuphold``, ``"$recrem"``, etc.)
   SRC_WIDTH  Width of SRC port
   DST_WIDTH  Width of DST port
   SRC_PEN    Source polarity filter enabled
   SRC_POL    Source polarity filter level
   DST_PEN    Destination polarity filter enabled
   DST_POL    Destination polarity filter level
   ========== ====================================================================

.. autocellgroup:: spec
   :members:
   :source:
   :linenos:
