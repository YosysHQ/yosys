FSM handling
============

The :cmd:ref:`fsm` command identifies, extracts, optimizes (re-encodes), and
re-synthesizes finite state machines. It again is a macro that calls a series of
other commands:

.. literalinclude:: /code_examples/macro_commands/fsm.ys
   :language: yoscrypt
   :start-after: #end:
   :caption: Passes called by :cmd:ref:`fsm`

See also :doc:`/cmd/fsm`.

The algorithms used for FSM detection and extraction are influenced by a more
general reported technique :cite:p:`fsmextract`.

FSM detection
~~~~~~~~~~~~~

The :cmd:ref:`fsm_detect` pass identifies FSM state registers. It sets the
``\fsm_encoding = "auto"`` attribute on any (multi-bit) wire that matches the
following description:

-  Does not already have the ``\fsm_encoding`` attribute.
-  Is not an output of the containing module.
-  Is driven by single ``$dff`` or ``$adff`` cell.
-  The ``\D``-Input of this ``$dff`` or ``$adff`` cell is driven by a
   multiplexer tree that only has constants or the old state value on its
   leaves.
-  The state value is only used in the said multiplexer tree or by simple
   relational cells that compare the state value to a constant (usually ``$eq``
   cells).

This heuristic has proven to work very well. It is possible to overwrite it by
setting ``\fsm_encoding = "auto"`` on registers that should be considered FSM
state registers and setting ``\fsm_encoding = "none"`` on registers that match
the above criteria but should not be considered FSM state registers.

Note however that marking state registers with ``\fsm_encoding`` that are not
suitable for FSM recoding can cause synthesis to fail or produce invalid
results.

FSM extraction
~~~~~~~~~~~~~~

The :cmd:ref:`fsm_extract` pass operates on all state signals marked with the
(``\fsm_encoding != "none"``) attribute. For each state signal the following
information is determined:

-  The state registers

-  The asynchronous reset state if the state registers use asynchronous reset

-  All states and the control input signals used in the state transition
   functions

-  The control output signals calculated from the state signals and control
   inputs

-  A table of all state transitions and corresponding control inputs- and
   outputs

The state registers (and asynchronous reset state, if applicable) is simply
determined by identifying the driver for the state signal.

From there the ``$mux-tree`` driving the state register inputs is recursively
traversed. All select inputs are control signals and the leaves of the
``$mux-tree`` are the states. The algorithm fails if a non-constant leaf that is
not the state signal itself is found.

The list of control outputs is initialized with the bits from the state signal.
It is then extended by adding all values that are calculated by cells that
compare the state signal with a constant value.

In most cases this will cover all uses of the state register, thus rendering the
state encoding arbitrary. If however a design uses e.g. a single bit of the
state value to drive a control output directly, this bit of the state signal
will be transformed to a control output of the same value.

Finally, a transition table for the FSM is generated. This is done by using the
ConstEval C++ helper class (defined in kernel/consteval.h) that can be used to
evaluate parts of the design. The ConstEval class can be asked to calculate a
given set of result signals using a set of signal-value assignments. It can also
be passed a list of stop-signals that abort the ConstEval algorithm if the value
of a stop-signal is needed in order to calculate the result signals.

The :cmd:ref:`fsm_extract` pass uses the ConstEval class in the following way to
create a transition table. For each state:

1. Create a ConstEval object for the module containing the FSM
2. Add all control inputs to the list of stop signals
3. Set the state signal to the current state
4. Try to evaluate the next state and control output
5. If step 4 was not successful:
   
   -  Recursively goto step 4 with the offending stop-signal set to 0.
   -  Recursively goto step 4 with the offending stop-signal set to 1.

6. If step 4 was successful: Emit transition

Finally a ``$fsm`` cell is created with the generated transition table and added
to the module. This new cell is connected to the control signals and the old
drivers for the control outputs are disconnected.

FSM optimization
~~~~~~~~~~~~~~~~

The :cmd:ref:`fsm_opt` pass performs basic optimizations on ``$fsm`` cells (not
including state recoding). The following optimizations are performed (in this
order):

-  Unused control outputs are removed from the ``$fsm`` cell. The attribute
   ``\unused_bits`` (that is usually set by the :cmd:ref:`opt_clean` pass) is
   used to determine which control outputs are unused.

-  Control inputs that are connected to the same driver are merged.

-  When a control input is driven by a control output, the control input is
   removed and the transition table altered to give the same performance without
   the external feedback path.

-  Entries in the transition table that yield the same output and only differ in
   the value of a single control input bit are merged and the different bit is
   removed from the sensitivity list (turned into a don't-care bit).

-  Constant inputs are removed and the transition table is altered to give an
   unchanged behaviour.

-  Unused inputs are removed.

FSM recoding
~~~~~~~~~~~~

The :cmd:ref:`fsm_recode` pass assigns new bit pattern to the states. Usually
this also implies a change in the width of the state signal. At the moment of
this writing only one-hot encoding with all-zero for the reset state is
supported.

The :cmd:ref:`fsm_recode` pass can also write a text file with the changes
performed by it that can be used when verifying designs synthesized by Yosys
using Synopsys Formality.
