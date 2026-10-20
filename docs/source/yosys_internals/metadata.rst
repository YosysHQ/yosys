Interned metadata
-----------------

Design
~~~~~~

Some attribute values are set on nearly every object and repeat across the
design. Storing them as ``Const`` strings in each object's ``attributes``
dictionary duplicates them many times over, and every merge of two objects
builds a new, longer string. Such attributes are instead interned per
``Design`` and stored outside the ``attributes`` dictionary, behind a small
handle. So far the only one is ``src``.

A ``src`` value is a set of source locations. Each location is an
``IdString`` in the design's ``TwinePool``: the file name is a leaf twine and
``:<line>.<column>-<line>.<column>`` is a suffix on it, so a file name is
stored once no matter how many locations point into it. A set is a
``SrcSet``, a sorted and deduplicated vector of such twines, interned in a
per-``Design`` ``SrcPool``. Like ``TwinePool``, ``SrcPool`` inherits from
``HashConsPool``, so equal sets are stored once.

Every ``AttrObject`` holds a 32-bit ``SrcRef`` index into that pool, or
``SrcRef::Null`` when it has no source location.

When a pass folds one object into another, the one it keeps takes on the
source locations of both:

.. code-block:: cpp
   :caption: Merging source locations in `opt_merge`
   :name: srcpool_merge

   module->design->merge_src(keep_cell, remove_cell);
   module->remove(remove_cell);

When it builds a new object out of others, it merges their handles instead, as
`share` does:

.. code-block:: cpp

   supercell->set_src(module->srcs().merge(c1->src(), c2->src()));

Merging is cheap and avoids touching any underlying strings. Location sets
are joined with ``|`` when rendered as a string, wuch as on export.

The integer behind a ``SrcRef`` depends on allocation order, so it must never
decide synthesis results. ``SrcRef`` therefore has no ordering, no hash and no
public accessor for its integer: it can't be a key of a ``dict`` or ``pool`` or
be sorted. ``SrcPool::Marks`` is a deduplicating set of ``SrcRef``\ s that
iterates in insertion order, for the few places that need it.

Sets are garbage collected in ``opt_clean``. Like an ``IdString``, a ``SrcRef`` held outside
the design is not a root, so it must not be kept across passes.

Migration from ``src`` attributes
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

C++ core change
^^^^^^^^^^^^^^^

``src`` is not in ``attributes`` anymore. ``has_attribute(ID::src)`` still
works, but ``get_string_attribute(ID::src)`` and
``set_string_attribute(ID::src, ...)`` assert. Read and write the handle
instead:

.. code-block:: diff

   -cell->attributes[ID::src] = "top.v:3.5-3.9";
   +cell->set_src(design->srcs().add("top.v:3.5-3.9"));

.. code-block:: diff

   -new_cell->set_src_attribute(cell->get_src_attribute());
   +new_cell->adopt_src_from(cell);

.. code-block:: diff

   -cell->add_strpool_attribute(ID::src, other->get_strpool_attribute(ID::src));
   +design->merge_src(cell, other);

``get_src_attribute()`` on ``Module``, ``Wire``, ``Memory``, ``Cell`` and
``Process``, or ``Design::get_src_attribute(obj)`` for any ``AttrObject``,
render the location as a string. ``Design::src_leaves(obj)`` returns the
individual locations.

The cell-creating ``Module`` helpers take a ``SrcRef`` instead of a string:

.. code-block:: diff

   -module->addAnd(NEW_ID, a, b, y, false, cell->get_src_attribute());
   +module->addAnd(NEW_ID, a, b, y, false, cell->src());

A ``SrcRef`` is valid only in its own ``Design``. ``Module::clone(Design *)``
re-interns source locations into the target design; elsewhere, use
``SrcPool::copy_from``:

.. code-block:: cpp

   dst->set_src(dst_design->srcs().copy_from(src_design->srcs(), src->src()));

Python helpers
^^^^^^^^^^^^^^

``pyosys`` exposes ``SrcRef`` as an opaque handle: ``SrcRef()`` and
``SrcRef.Null`` are the null handle, handles compare with ``==`` and can't be
hashed. ``srcs()`` on ``Design``, ``Module``, ``Wire``, ``Memory``, ``Cell``
and ``Process`` returns the design's pool, which offers ``add``, ``merge``,
``str`` and ``leaves``.

.. code-block:: diff

   -cell.set_src_attribute("top.v:3.5-3.9")
   +cell.set_src(design.srcs().add("top.v:3.5-3.9"))

.. code-block:: diff

   -module.addAnd("\\and", a, b, y, src=cell.get_src_attribute())
   +module.addAnd("\\and", a, b, y, src_ref=cell.src())

``cell.get_src_attribute()`` still returns the location as a string.

RTLIL
^^^^^

``write_rtlil`` refers to source locations instead of spelling them out. A
single location is written as ``@<twine>``, a reference into the ``twines``
section. A set of several locations is written as ``$<set>``, a reference
into a new ``srcs`` section with one ``set <set> <twine>...`` line per set:

.. code-block:: text

   srcs
     set 0 1055 1056
   end
   ...
     attribute \src "$0"  # top.v:3.5-3.9|top.v:4.5-4.9
     attribute \src "@1055"  # top.v:3.5-3.9

``read_rtlil`` still accepts plain location strings, so older RTLIL files can
be read in. ``write_rtlil -readable`` writes plain strings for older Yosys
versions.
