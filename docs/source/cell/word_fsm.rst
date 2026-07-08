Finite state machines
---------------------

The `$fsm` cell represents a finite state machine. It is created by the
``fsm_extract`` pass and encodes both the state encoding and the transition
table as parameters.

.. table:: Ports

   ========= ======== ================ ============================================
   Port      Dir      Width            Description
   ========= ======== ================ ============================================
   CLK       input    1                Clock signal
   ARST      input    1                Asynchronous reset
   CTRL_IN   input    CTRL_IN_WIDTH    Input control signals (conditions)
   CTRL_OUT  output   CTRL_OUT_WIDTH   Output control signals (actions)
   ========= ======== ================ ============================================

.. table:: Parameters

   ================ =========================================================
   Parameter        Description
   ================ =========================================================
   NAME             Name of the FSM (for identification)
   CLK_POLARITY     Clock polarity: 1 for posedge, 0 for negedge
   ARST_POLARITY    Reset polarity: 1 for active-high, 0 for active-low
   CTRL_IN_WIDTH    Width of the CTRL_IN port
   CTRL_OUT_WIDTH   Width of the CTRL_OUT port
   STATE_BITS       Number of bits per state encoding
   STATE_NUM        Number of states
   STATE_NUM_LOG2   Ceiling log2 of STATE_NUM (bits needed to index a state)
   STATE_RST        Index of the reset state
   STATE_TABLE      Concatenated state encodings (STATE_BITS * STATE_NUM bits)
   TRANS_NUM        Number of transitions
   TRANS_TABLE      Concatenated transition entries; each entry contains the
                    current state index, next state index, input conditions,
                    and output values
   ================ =========================================================

The `$fsm` cell is typically lowered back to registers and logic by the
``fsm_map`` pass.

.. autocellgroup:: fsm
   :members:
   :source:
   :linenos:
