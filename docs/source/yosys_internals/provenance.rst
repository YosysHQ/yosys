Index provenance
----------------

``IdString`` and ``SrcRef`` are indices into per-``Design`` pools, see
:doc:`idstring` and :doc:`metadata`. An index used with the wrong pool does not
fail on its own: it reads whatever that pool stores at the same position, or a
slot that garbage collection has already freed. Such bugs silently produce
wrong names or source locations, typically only once a second ``Design`` is
involved.

Configure with ``-DYOSYS_ENABLE_INDEX_PROVENANCE=ON`` to catch them. Every
``TwinePool`` gets a serial number, and every index a design hands out is
stamped with the serial of its ``TwinePool``:

- ``IdString`` grows from 32 to 64 bits to carry the serial.
  ``TwinePool::check_owned`` asserts that a name belongs to the pool it is
  used with. ``Design::module``, ``Design::has``, ``Module::wire`` and
  ``Module::cell`` check their argument.
- ``SrcRef`` carries the serial next to its 32-bit index. ``SrcPool`` asserts
  on every lookup that a handle is its own and that its set is still alive.
  Garbage collection looks up every handle reachable from the design, so a
  foreign or stale ``SrcRef`` stored on an object is reported at the next
  collection at the latest.

Indices with serial 0 are accepted by every pool. These are the static names
of ``kernel/constids.inc`` and the null handles.

A copy of a pool gets a new serial, for example when ``Design::clone_into``
copies a design. Indices therefore have to be translated into the copy with
``copy_from``, which stamps them with the new serial. ``Module::clone`` does
this for names and source locations.

The checks cost time and memory and are meant for debugging only, so they are
off by default. The stamp does not take part in comparisons, so results are
the same with and without the checks.
