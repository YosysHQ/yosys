Staged formal with witness replay
=================================

This guide documents a simple two-stage flow for chaining formal runs via a
saved witness and replaying it into a new initial state. The example in
``tests/formal_witness_replay`` uses the Verific frontend for SystemVerilog/SVA;
set ``YOSYS`` to a Verific-enabled binary (for example
``../yosys-private/install/bin/yosys``) when running the scripts.

Overview
--------

- Stage 1: run a cover/BMC proof that reaches an interesting waypoint and dump a
  Yosys witness (``.yw``).
- Replay: use ``sim -w`` to apply the witness to the original design, writing a
  new RTLIL with baked-in init values.
- Stage 2: reload that RTLIL, activate a different set of properties, and
  continue proving/covering from the saved state.

Flow contract
-------------

- The RTL must stay identical across stages. Only the active property set and
  INIT values may change.
- Use phase (or other) attributes to drop properties not meant for a given
  stage; e.g. ``select */a:phase */a:phase=1 %d; delete`` before Stage 1.
- Prefer YW over VCD: YW records solver-provided data with ``hdlname`` mapping,
  so signal names stay stable through flattening and ``prep``.
- ``sim -w`` writes back flip-flop and memory state; ``-a`` can be added to
  include internal ``$`` wires in generated traces, but it does not change how a
  YW witness is applied.
- Environment-controlled signals should be inputs or ``anyseq``; ``sim`` only
  drives inputs, while the solver may assign ``anyseq`` nets.
- For later stages consider ``sim -noinitstate`` if you do not want ``$initstate``
  to fire again.

Example commands (from tests/formal_witness_replay)
---------------------------------------------------

Stage 1 preparation and cover run::

  yosys -p '
    read_verilog -formal tests/formal_witness_replay/dut.sv;
    prep -top dut; flatten;
    write_rtlil stage_1_init.il'

  yosys -p '
    read_rtlil stage_1_init.il;
    select */a:phase */a:phase=1 %d; delete;
    write_rtlil stage_1_fv.il'

  # stage_1.sby uses "mode cover" with smtbmc to produce stage_1/engine_0/trace0.yw

Replay the witness into a new init-state IL::

  yosys -p '
    read_rtlil stage_1_init.il;
    prep -top dut;
    sim -w -a -scope dut -r stage_1/engine_0/trace0.yw;
    write_rtlil stage_2_init.il'

Stage 2 cover run (only phase 2 properties active)::

  yosys -p '
    read_rtlil stage_2_init.il;
    select */a:phase */a:phase=2 %d; delete;
    write_rtlil stage_2_fv.il'

  # stage_2.sby then proves the pending ack cover starting from the baked state

Notes and caveats
-----------------

- YW is input-only for ``sim``; the pass never writes a YW file. Use VCD/FST/AIW
  output if you need a trace of the replay itself.
- Cross-stage sequential assumptions may need care. If an assumption spans
  cycles across the stage boundary, you may need to extend the witness during FV
  and trim it before replay so the assumption is fully evaluated.
- Keep a single RTL source with property guards so that signal names stay
  stable; changing the HDL between stages will break witness replay.
