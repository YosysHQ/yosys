.. _sec:attributes:

Attributes
----------

Attributes are a mechanism of Verilog and similar languages
to provide various kinds of information from the user
to EDA tools like Yosys. Yosys then "understands" some of them,
and does its best to keep the rest untouched.
See :doc:`/using_yosys/verilog` for the list of attributes Yosys understands.

Among the attributes Yosys understands, some kinds are worth telling apart
by what is lost when one is discarded:

- *Semantic attributes* are part of what the design means. Discarding one
  changes the function a module implements. Examples are ``init``,
  ``anyseq``, ``full_case`` and ``parallel_case``.
- *Optimization metadata* can change the
  quality of the result, for example the area of a synthesized chip,
  but don't directly control module function so dropping them can't
  make the synthesized result logically incorrect.
  An example is ``keep``.
- *Debug metadata* exist only to be helpful. Losing them might be
  disappointing and break scripts that expect it not to happen, but their
  presence, absence or value is never going to affect correctness or quality.
  Examples are ``src``, ``hdlname`` and ``scopename``.

Generally attributes are internally implemented as integer or string constants,
but some debug metadata has a special implementation that makes it
easier and more efficient for Yosys to work with.
We call these attributes "specialized".

.. _sec:specialized_attributes:

Specialized attributes
----------------------

Some attribute values are set on nearly every object and repeat across the
design. Storing them as ``Const`` strings in each object's ``attributes``
dictionary duplicates them many times over, and every merge of two objects
builds a new, longer string. Such attributes are instead interned per
``Design`` and stored outside the ``attributes`` dictionary, behind a small
ref. So far these are ``src``, ``hdlname`` and ``scopename``.

.. _sec:source_locations:

Source locations
~~~~~~~~~~~~~~~~

A ``src`` value is a set of source locations. Each location is an
``IdString``, intended to be a line/column range suffix like
``:<line>.<column>-<line>.<column>`` of a file path ``IdString``.
A set is a
``TwineSet``, a sorted and deduplicated vector of such twines, interned in a
per-``Design`` ``SrcPool``.

Every ``AttrObject`` holds a 32-bit ``SrcRef`` into that pool, or
``SrcRef::Null`` when it has no source location.

Location sets are joined with ``|`` when rendered as a string, such as on
export.

The integer behind a ``SrcRef`` depends on allocation order, so it must never
decide synthesis results. ``SrcRef`` therefore has no ordering, no hash and no
public accessor for its integer: it can't be a key of a ``dict`` or ``pool`` or
be sorted. ``SrcPool::Marks`` is a deduplicating set of ``SrcRef``\ s that
iterates in insertion order, for the few places that need it.

Sets are garbage collected in `opt_clean`. Like an ``IdString``, a ``SrcRef`` held outside
the design is not a root, so it must not be kept across passes. A ``SrcRef``
used with the wrong design or after its set was collected is caught by the
checks described in :doc:`provenance`.

.. _sec:hdl_names:

Names
~~~~~

``hdlname`` and ``scopename`` live in a per-``Design`` ``MetaPool``. Every
``AttrObject`` holds a 32-bit ``MetaRef`` into it, or ``MetaRef::Null``. The
metadata block it refers to holds the object's identity, a scope and a name,
plus the names it absorbed from other objects. Like ``SrcPool``, ``MetaPool``
inherits from ``HashConsPool``, so equal blocks are stored once.

A scope is a chain of twines in the design's ``TwinePool``: ``a b`` is the
suffix `` b`` on the scope ``a``, so all names in one scope share it. Every
chain starts at an empty root twine, so a single-element ``hdlname``, such as a
module's original name, is a name in the root scope. The name is a suffix on
its scope that holds only the last element.

An identity with a name renders as the ``hdlname`` attribute, and one without
renders as ``scopename``. Absorbed names have no attribute and only
`write_rtlil` writes them out.

.. _sec:moving_metadata:

Moving metadata between objects
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

There are two ways to move specialized attributes between objects in a pass. An
object that replaces another takes over its metadata:

.. code-block:: cpp

   design->transfer_metadata(new_obj, old_obj);

An object that takes in others without replacing them absorbs their metadata:

.. code-block:: cpp
   :caption: Absorbing metadata in `opt_merge`
   :name: srcpool_merge

   module->design->absorb_metadata(keep_cell, remove_cell);
   module->remove(remove_cell);

For ``src``, a transfer copies the source's locations and absorbing adds them
to the target's.

For names, a transfer replaces the target's identity with the source's and adds
the target's old identity and the source's absorbed names to the target's
absorbed names. Absorbing adds the source's identity and absorbed names to the
target's absorbed names. The parts of a split object, such as the bits of a
sliced flip-flop, each carry the identity, since the HDL has no object for a
part.

A pass that only needs to combine source locations, such as `share` building a
new cell out of two, merges the refs directly. Merging is cheap and avoids
touching any underlying strings:

.. code-block:: cpp

   supercell->set_src(module->srcs().merge(c1->src(), c2->src()));

.. _sec:metadata_migration:

Migration from ``src``, ``hdlname`` and ``scopename`` attributes
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

C++ core change
^^^^^^^^^^^^^^^

``src`` is not in ``attributes`` anymore. ``has_attribute(ID::src)`` still
works, but ``get_string_attribute(ID::src)`` and
``set_string_attribute(ID::src, ...)`` assert. Read and write the ref
instead:

.. code-block:: diff

   -cell->attributes[ID::src] = "top.v:3.5-3.9";
   +cell->set_src(design->srcs().add("top.v:3.5-3.9"));

.. code-block:: diff

   -new_cell->set_src_attribute(cell->get_src_attribute());
   +design->transfer_metadata(new_cell, cell);

.. code-block:: diff

   -cell->add_strpool_attribute(ID::src, other->get_strpool_attribute(ID::src));
   +design->absorb_metadata(cell, other);

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

``hdlname`` and ``scopename`` are not in ``attributes`` anymore either.
``has_attribute`` still works for them, but ``get_string_attribute`` and
``set_string_attribute`` assert. Use ``get_hdlname_attribute()`` and
``set_hdlname_attribute()`` on ``Module``, ``Wire``, ``Memory``, ``Cell`` and
``Process``, or ``Design::get_hdlname``, ``set_hdlname``, ``get_scopename`` and
``set_scopename`` for any ``AttrObject``:

.. code-block:: diff

   -scope = cell->get_string_attribute(ID(scopename));
   +scope = design->get_scopename(cell);

Copying a whole ``attributes`` dictionary no longer copies the names along with
it. Copy with ``transfer_attributes``, or pair the copy with ``absorb_metadata``.

``RTLIL::specialized_attributes`` lists ``src``, ``hdlname`` and ``scopename``,
and ``Design::get_specialized_attribute`` and ``set_specialized_attribute`` read and
write any of them by name. Frontends set attributes read from their input with
``import_attribute`` or ``import_attributes`` from
``kernel/metadata/attributes.h``, which route the specialized ones:

.. code-block:: diff

   -obj->attributes[id] = value;
   +import_attribute(design, obj, id, value);

Backends iterate ``ExportedAttributes`` from ``kernel/metadata/attributes.h``,
which yields the specialized attributes rendered as strings, then the object's
``attributes``:

.. code-block:: diff

   -for (auto &[name, value] : obj->attributes)
   +for (auto &[name, value] : ExportedAttributes(design, obj))

Python helpers
^^^^^^^^^^^^^^

``pyosys`` exposes ``SrcRef`` as an opaque ref: ``SrcRef()`` and
``SrcRef.Null`` are the null ref, refs compare with ``==`` and can't be
hashed. ``srcs()`` on ``Design``, ``Module``, ``Wire``, ``Memory``, ``Cell``
and ``Process`` returns the design's pool, which offers ``add``, ``merge``,
``str`` and ``leaves``.

.. code-block:: diff

   -cell.set_src_attribute("top.v:3.5-3.9")
   +cell.set_src(design.srcs().add("top.v:3.5-3.9"))

.. code-block:: diff

   -module.addAnd("\\and", a, b, y, src=cell.get_src_attribute())
   +module.addAnd("\\and", a, b, y, src=cell.src())

``cell.get_src_attribute()`` still returns the location as a string.

RTLIL
^^^^^

`write_rtlil` refers to specialized attributes instead of spelling them out.
Everything it refers to is written once, in a ``metadata`` section after
``autoidx``. The section is for names and metadata: it holds a ``twines``
section, a ``srcs`` section of location sets, a ``namesets`` section of
absorbed name sets and a ``blocks`` section of metadata blocks:

.. code-block:: text

   metadata
     twines
       root 1030 ""
       suffix 1031 1030 "top"
       suffix 1064 1031 " u_and"
       ...
     end
     srcs
       set 0 1055 1056
     end
     namesets
       set 0 1064
     end
     blocks
       block 1 scope 1031
       block 2 hdlnames 0
     end
   end

A single source location is written as ``@<twine>`` and a set of several as
``$<set>``. An object's metadata block is written as ``#<block>`` on a
``metadata`` attribute, followed by its names as a comment:

.. code-block:: text

     attribute \src "$0"  # top.v:3.5-3.9|top.v:4.5-4.9
     attribute \src "@1055"  # top.v:3.5-3.9
     attribute \metadata "#1"  # scopename "top"
     attribute \metadata "#2"  # absorbed "top u_and"

`read_rtlil` still accepts plain ``src``, ``hdlname`` and ``scopename``
strings, so older RTLIL files can be read in. :yoscrypt:`write_rtlil -readable` writes
plain strings for older Yosys versions and drops absorbed names.
