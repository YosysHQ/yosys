Formal verification cells
-------------------------

.. role:: yoscrypt(code)
   :language: yoscrypt

.. note::

   Some front-ends may not support the generic `$check` cell, in such cases
   calling :yoscrypt:`chformal -lower` will convert each `$check` cell into it's
   equivalent.  See `chformal` for more.

Property cells
~~~~~~~~~~~~~~

The simple property cells `$assert`, `$assume`, `$live`, `$fair`, and `$cover`
all share the same two-port interface:

.. table:: Ports (property cells)

   ===== ======== ===== =====================================================
   Port  Dir      Width Description
   ===== ======== ===== =====================================================
   A     input    1     The property signal
   EN    input    1     Enable: property is only active when EN is high
   ===== ======== ===== =====================================================

- `$assert`: the property ``A`` must hold (be 1) whenever ``EN`` is high.
- `$assume`: constrains the environment so that ``A`` is assumed true whenever ``EN`` is high.
- `$live`: liveness property — ``A`` must eventually become true.
- `$fair`: fairness constraint — ``A`` must be true infinitely often.
- `$cover`: coverage point — records that the condition ``A && EN`` was reached.

The `$check` cell is a generic property cell that subsumes all of the above.
Its ``FLAVOR`` parameter selects the type: ``"assert"``, ``"assume"``,
``"live"``, ``"fair"``, or ``"cover"``. It extends the interface with a trigger
and a format string for error messages.

.. table:: Ports ($check)

   ===== ======== ============== =============================================
   Port  Dir      Width          Description
   ===== ======== ============== =============================================
   A     input    1              Property signal
   EN    input    1              Enable
   TRG   input    TRG_WIDTH      Trigger signals (clock edges for clocked props)
   ARGS  input    ARGS_WIDTH     Arguments for the FORMAT string
   ===== ======== ============== =============================================

.. table:: Parameters ($check)

   ============= ==============================================================
   Parameter     Description
   ============= ==============================================================
   FLAVOR        Property type: ``"assert"``, ``"assume"``, ``"live"``,
                 ``"fair"``, or ``"cover"``
   FORMAT        printf-style format string for failure messages
   ARGS_WIDTH    Total bit width of ARGS
   TRG_ENABLE    1 if triggered by explicit clock edges, 0 for combinational
   TRG_WIDTH     Number of trigger signals
   TRG_POLARITY  Polarity of each trigger (1=posedge, 0=negedge), one bit each
   PRIORITY      Priority for ordering of checks
   ============= ==============================================================

.. note::

   Some front-ends generate `$assert`, `$assume`, etc. directly. The
   ``chformal -lower`` command converts each `$check` cell into the
   corresponding simple property cell.

Non-deterministic value cells
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

These cells produce non-deterministic outputs, used to model free inputs in
formal verification.

- `$anyconst` (``Y`` output, ``WIDTH`` parameter): outputs an arbitrary
  **constant** value chosen non-deterministically. The value does not change
  over time. Used to model an unknown but fixed parameter.

- `$anyseq` (``Y`` output, ``WIDTH`` parameter): outputs an arbitrary
  **sequence** of values, potentially changing each clock cycle. Used to model
  an unconstrained input signal.

- `$allconst` (``Y`` output, ``WIDTH`` parameter): dual of `$anyconst` for
  universal quantification — the property must hold for **all** constant values.

- `$allseq` (``Y`` output, ``WIDTH`` parameter): dual of `$anyseq` for
  universal quantification — the property must hold for **all** sequences.

- `$anyinit` (``D`` input and ``Q`` output, ``WIDTH`` parameter): a flip-flop
  whose initial value is non-deterministic. Unlike `$anyconst`, only the
  initial value is free; afterwards ``Q`` follows ``D`` on each clock cycle.

Other formal cells
~~~~~~~~~~~~~~~~~~

The `$equiv` cell is used during equivalence checking to assert that two
signals carry the same value.

.. table:: Ports ($equiv)

   ===== ======== ===== =====================================================
   Port  Dir      Width Description
   ===== ======== ===== =====================================================
   A     input    1     Signal from the first (reference) circuit
   B     input    1     Signal from the second (modified) circuit
   Y     output   1     Result: A when A == B, x (undefined) otherwise
   ===== ======== ===== =====================================================

The `$initstate` cell outputs a 1 during the initial state of a formal
verification run and 0 on all subsequent cycles. It takes no inputs and has a
single output ``Y``.

Clock cells
~~~~~~~~~~~

The `$ff` cell is a word-level D-type flip-flop clocked by the implicit global
clock used in formal verification.

.. table:: Ports ($ff)

   ===== ======== ========= ===================
   Port  Dir      Width     Description
   ===== ======== ========= ===================
   D     input    WIDTH     Data input
   Q     output   WIDTH     Registered output
   ===== ======== ========= ===================

.. table:: Parameters ($ff)

   ========= =====================================
   Parameter Description
   ========= =====================================
   WIDTH     Width of D and Q ports
   ========= =====================================

The `$_FF_` cell is the gate-level (1-bit) equivalent of `$ff`, clocked by
``$global_clock``. It has ports ``D`` (input) and ``Q`` (output) and no
parameters. It is used in netlists for formal verification.

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
