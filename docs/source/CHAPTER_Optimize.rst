.. _chapter:opt:

Optimizations
=============

Yosys employs a number of optimizations to generate better and cleaner results.
This chapter outlines these optimizations.

Simple optimizations
--------------------

The Yosys pass opt runs a number of simple optimizations. This includes removing
unused signals and cells and const folding. It is recommended to run this pass
after each major step in the synthesis script. At the time of this writing the
opt pass executes the following passes that each perform a simple optimization:

-  Once at the beginning of opt:

   -  opt_expr
   -  opt_merge -nomux

-  Repeat until result is stable:

   -  opt_muxtree
   -  opt_reduce
   -  opt_merge
   -  opt_rmdff
   -  opt_clean
   -  opt_expr

The following section describes each of the opt\_ passes.

The opt_expr pass
~~~~~~~~~~~~~~~~~

This pass performs const folding on the internal combinational cell types
described in :numref:`Chap. %s <chapter:celllib>`. This means a cell with all
constant inputs is replaced with the constant value this cell drives. In some
cases this pass can also optimize cells with some constant inputs.

.. table:: Const folding rules for $_AND\_ cells as used in opt_expr.
   :name: tab:opt_expr_and
   :align: center

   ========= ========= ===========
   A-Input   B-Input   Replacement
   ========= ========= ===========
   any       0         0
   0         any       0
   1         1         1
   --------- --------- -----------
   X/Z       X/Z       X
   1         X/Z       X
   X/Z       1         X
   --------- --------- -----------
   any       X/Z       0
   X/Z       any       0
   --------- --------- -----------
   :math:`a` 1         :math:`a`
   1         :math:`b` :math:`b`
   ========= ========= ===========

.. How to format table?

:numref:`Table %s <tab:opt_expr_and>` shows the replacement rules used for
optimizing an $_AND\_ gate. The first three rules implement the obvious const
folding rules. Note that ‘any' might include dynamic values calculated by other
parts of the circuit. The following three lines propagate undef (X) states.
These are the only three cases in which it is allowed to propagate an undef
according to Sec. 5.1.10 of IEEE Std. 1364-2005 :cite:p:`Verilog2005`.

The next two lines assume the value 0 for undef states. These two rules are only
used if no other substitutions are possible in the current module. If other
substitutions are possible they are performed first, in the hope that the ‘any'
will change to an undef value or a 1 and therefore the output can be set to
undef.

The last two lines simply replace an $_AND\_ gate with one constant-1 input with
a buffer.

Besides this basic const folding the opt_expr pass can replace 1-bit wide $eq
and $ne cells with buffers or not-gates if one input is constant.

The opt_expr pass is very conservative regarding optimizing $mux cells, as these
cells are often used to model decision-trees and breaking these trees can
interfere with other optimizations.

The opt_muxtree pass
~~~~~~~~~~~~~~~~~~~~

This pass optimizes trees of multiplexer cells by analyzing the select inputs.
Consider the following simple example:

.. code:: verilog
   :number-lines:

   module uut(a, y); input a; output [1:0] y = a ? (a ? 1 : 2) : 3; endmodule

The output can never be 2, as this would require ``a`` to be 1 for the outer
multiplexer and 0 for the inner multiplexer. The opt_muxtree pass detects this
contradiction and replaces the inner multiplexer with a constant 1, yielding the
logic for ``y = a ? 1 : 3``.

The opt_reduce pass
~~~~~~~~~~~~~~~~~~~

This is a simple optimization pass that identifies and consolidates identical
input bits to $reduce_and and $reduce_or cells. It also sorts the input bits to
ease identification of shareable $reduce_and and $reduce_or cells in other
passes.

This pass also identifies and consolidates identical inputs to multiplexer
cells. In this case the new shared select bit is driven using a $reduce_or cell
that combines the original select bits.

Lastly this pass consolidates trees of $reduce_and cells and trees of $reduce_or
cells to single large $reduce_and or $reduce_or cells.

These three simple optimizations are performed in a loop until a stable result
is produced.

The opt_rmdff pass
~~~~~~~~~~~~~~~~~~

This pass identifies single-bit d-type flip-flops ($_DFF\_, $dff, and $adff
cells) with a constant data input and replaces them with a constant driver.

The opt_clean pass
~~~~~~~~~~~~~~~~~~

This pass identifies unused signals and cells and removes them from the design.
It also creates an ``\unused_bits`` attribute on wires with unused bits. This
attribute can be used for debugging or by other optimization passes.

The opt_merge pass
~~~~~~~~~~~~~~~~~~

This pass performs trivial resource sharing. This means that this pass
identifies cells with identical inputs and replaces them with a single instance
of the cell.

The option -nomux can be used to disable resource sharing for multiplexer cells
($mux and $pmux. This can be useful as it prevents multiplexer trees to be
merged, which might prevent opt_muxtree to identify possible optimizations.

FSM extraction and encoding
---------------------------

The fsm pass performs finite-state-machine (FSM) extraction and recoding. The
fsm pass simply executes the following other passes:

-  Identify and extract FSMs:

   -  fsm_detect
   -  fsm_extract

-  Basic optimizations:

   -  fsm_opt
   -  opt_clean
   -  fsm_opt

-  Expanding to nearby gate-logic (if called with -expand):

   -  fsm_expand
   -  opt_clean
   -  fsm_opt

-  Re-code FSM states (unless called with -norecode):

   -  fsm_recode

-  Print information about FSMs:

   -  fsm_info

-  Export FSMs in KISS2 file format (if called with -export):

   -  fsm_export

-  Map FSMs to RTL cells (unless called with -nomap):

   -  fsm_map

The fsm_detect pass identifies FSM state registers and marks them using the
``\fsm_encoding = "auto"`` attribute. The fsm_extract extracts all FSMs marked
using the ``\fsm_encoding`` attribute (unless ``\fsm_encoding`` is set to
"none") and replaces the corresponding RTL cells with a $fsm cell. All other
fsm\_ passes operate on these $fsm cells. The fsm_map call finally replaces the
$fsm cells with RTL cells.

Note that these optimizations operate on an RTL netlist. I.e. the fsm pass
should be executed after the proc pass has transformed all RTLIL::Process
objects to RTL cells.

The algorithms used for FSM detection and extraction are influenced by a more
general reported technique :cite:p:`fsmextract`.

FSM detection
~~~~~~~~~~~~~

The fsm_detect pass identifies FSM state registers. It sets the ``\fsm_encoding
= "auto"`` attribute on any (multi-bit) wire that matches the following
description:

-  Does not already have the ``\fsm_encoding`` attribute.
-  Is not an output of the containing module.
-  Is driven by single $dff or $adff cell.
-  The ``\D``-Input of this $dff or $adff cell is driven by a multiplexer tree
   that only has constants or the old state value on its leaves.
-  The state value is only used in the said multiplexer tree or by simple
   relational cells that compare the state value to a constant (usually $eq
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

The fsm_extract pass operates on all state signals marked with the
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

From there the $mux-tree driving the state register inputs is recursively
traversed. All select inputs are control signals and the leaves of the $mux-tree
are the states. The algorithm fails if a non-constant leaf that is not the state
signal itself is found.

The list of control outputs is initialized with the bits from the state signal.
It is then extended by adding all values that are calculated by cells that
compare the state signal with a constant value.

In most cases this will cover all uses of the state register, thus rendering the
state encoding arbitrary. If however a design uses e.g. a single bit of the
state value to drive a control output directly, this bit of the state signal
will be transformed to a control output of the same value.

Finally, a transition table for the FSM is generated. This is done by using the
ConstEval C++ helper class (defined in kernel/consteval.h) that can be used to
evaluate parts of the design. The ConstEval class can be asked to calculate a
given set of result signals using a set of signal-value assignments. It can also
be passed a list of stop-signals that abort the ConstEval algorithm if the value
of a stop-signal is needed in order to calculate the result signals.

The fsm_extract pass uses the ConstEval class in the following way to create a
transition table. For each state:

1. Create a ConstEval object for the module containing the FSM
2. Add all control inputs to the list of stop signals
3. Set the state signal to the current state
4. Try to evaluate the next state and control output
5. If step 4 was not successful:
   
   -  Recursively goto step 4 with the offending stop-signal set to 0.
   -  Recursively goto step 4 with the offending stop-signal set to 1.

6. If step 4 was successful: Emit transition

Finally a $fsm cell is created with the generated transition table and added to
the module. This new cell is connected to the control signals and the old
drivers for the control outputs are disconnected.

FSM optimization
~~~~~~~~~~~~~~~~

The fsm_opt pass performs basic optimizations on $fsm cells (not including state
recoding). The following optimizations are performed (in this order):

-  Unused control outputs are removed from the $fsm cell. The attribute
   ``\unused_bits`` (that is usually set by the opt_clean pass) is used to
   determine which control outputs are unused.

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

The fsm_recode pass assigns new bit pattern to the states. Usually this also
implies a change in the width of the state signal. At the moment of this writing
only one-hot encoding with all-zero for the reset state is supported.

The fsm_recode pass can also write a text file with the changes performed by it
that can be used when verifying designs synthesized by Yosys using Synopsys
Formality .

Logic optimization
------------------

Yosys can perform multi-level combinational logic optimization on gate-level
netlists using the external program ABC . The abc pass extracts the
combinational gate-level parts of the design, passes it through ABC, and
re-integrates the results. The abc pass can also be used to perform other
operations using ABC, such as technology mapping (see :numref:`Sec %s
<sec:techmap_extern>` for details).
