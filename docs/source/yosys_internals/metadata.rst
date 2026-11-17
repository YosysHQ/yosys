Interned metadata
-----------------

Design
~~~~~~

Some attribute values are set on nearly every object and repeat across the
design. Storing them as ``Const`` strings in each object's ``attributes``
dictionary duplicates them many times over, and every merge of two objects
builds a new, longer string. Such attributes are instead interned per
``Design`` and stored outside the ``attributes`` dictionary, behind a small
handle. So far the only one is ``src``. Commands and frontends that take
attribute names from users or files, such as `select`, `setattr`, the Tcl
attribute commands and the JSON frontend, recognize such names with
``Design::is_metadata`` and read and write their values as strings with
``Design::get_metadata_string`` and ``Design::set_metadata_string``.

A ``src`` value is a set of source locations. Each location is an
``IdString`` in the design's ``TwinePool``: the file name is a root twine and
``:<line>.<column>-<line>.<column>`` is a suffix on it, so a file name is
stored once no matter how many locations point into it. A set is a
``SrcSet``, a sorted and deduplicated vector of such twines, interned in a
per-``Design`` ``SrcPool``. Like ``TwinePool``, ``SrcPool`` inherits from
``HashConsPool``, so equal sets are stored once.

A frontend that knows the file, line and column of a location builds it with
``SrcPool::file`` and ``SrcPool::location`` and interns one or more such
locations as a set with ``SrcPool::add``.

``SrcPool::add_parsed`` takes a location string in the format of the old ``src``
attribute and splits it. It splits the string on ``|`` into locations, and
each location at its last ``:`` into the file name and the suffix. A location
without such a colon becomes a single root twine. As with the old attribute,
a file name containing ``|`` can't be represented.

Every ``AttrObject`` holds a 32-bit ``SrcRef`` index into that pool, or
``SrcRef::Null`` when it has no source location.

Passes move metadata between objects with one of two operations. An object
that replaces another takes over its metadata and becomes the sole carrier of
its identity:

.. code-block:: cpp

   design->transfer_metadata(new_obj, old_obj);

An object that takes in others without replacing them absorbs their metadata
as a non-unique use, as the cell that `opt_merge` keeps absorbs its removed
twin:

.. code-block:: cpp
   :caption: Absorbing metadata in `opt_merge`
   :name: srcpool_merge

   module->design->absorb_metadata(keep_cell, remove_cell);
   module->remove(remove_cell);

For ``src``, a transfer copies the source's locations and absorbing adds them
to the target's.

When a pass builds a new object out of others, it merges their handles
instead, as `share` does:

.. code-block:: cpp

   supercell->set_src(module->srcs().merge(c1->src(), c2->src()));

Merging is cheap and avoids touching any underlying strings. Location sets
are joined with ``|`` in file, line and column order when rendered as a
string, such as on export.

The integer behind a ``SrcRef`` depends on allocation order, so it must never
decide synthesis results. ``SrcRef`` therefore has no ordering, no hash and no
public accessor for its integer: it can't be a key of a ``dict`` or ``pool`` or
be sorted. ``SrcPool::Marks`` is a deduplicating set of ``SrcRef``\ s that
iterates in insertion order, for the few places that need it.

Sets are garbage collected in `opt_clean`. Like an ``IdString``, a ``SrcRef`` held outside
the design is not a root, so it must not be kept across passes.

Migration from ``src`` attributes
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

C++ core change
^^^^^^^^^^^^^^^

``src`` is not in ``attributes`` anymore. The ``AttrObject`` attribute
methods, such as ``has_attribute``, ``get_bool_attribute`` and
``get_string_attribute``, assert when given ``ID::src``. Read and write the
handle instead:

.. code-block:: diff

   -cell->attributes[ID::src] = "top.v:3.5-3.9";
   +cell->set_src(design->srcs().add_parsed("top.v:3.5-3.9"));

.. code-block:: diff

   -new_cell->set_src_attribute(cell->get_src_attribute());
   +design->transfer_metadata(new_cell, cell);

.. code-block:: diff

   -cell->add_strpool_attribute(ID::src, other->get_strpool_attribute(ID::src));
   +design->absorb_metadata(cell, other);

``set_src_attribute()``, ``get_src_attribute()``, ``set_strpool_attribute()``
and ``add_strpool_attribute()`` are gone. To set a location from a string,
intern it. To get it as a string, render it with the pool:

.. code-block:: diff

   -cell->set_src_attribute(src);
   +cell->set_src(design->srcs().add_parsed(src));

.. code-block:: diff

   -std::string src = cell->get_src_attribute();
   +std::string src = cell->srcs().str(cell->src());

``SrcPool::locations`` returns the location twines of a set, in storage order
rather than the sorted order of ``SrcPool::str``:

.. code-block:: diff

   -for (auto &s : cell->get_strpool_attribute(ID::src))
   +for (IdString loc : cell->srcs().locations(cell->src()))
   +	std::string s = cell->twines().str(loc);

To test for a location, use ``has_src``:

.. code-block:: diff

   -if (cell->has_attribute(ID::src))
   +if (cell->has_src())

The cell-creating ``Module`` helpers take a ``SrcRef`` instead of a string:

.. code-block:: diff

   -module->addAnd(NEW_ID, a, b, y, false, cell->get_src_attribute());
   +module->addAnd(NEW_ID, a, b, y, false, cell->src());

``Module::addCell(name, other)``, ``addMemory(name, other)``,
``addProcess(name, other)`` and ``Module::clone`` copy the source location
along with the object, so there is no need to copy it again afterwards.
``FfData`` carries the location of a flip-flop in ``FfData::src``, next to
``attributes``, and ``FfData::emit`` sets it on the new cell.

Inside processes, ``SyncAction::src``, ``CaseRule::compare_src`` and
``SwitchRule::signal_src`` are ``SrcRef``\ s too, and ``Process::walk_srcs``
visits all of them. ``CaseRule`` and ``SwitchRule`` know their module, so they
are constructed with it, and ``clone`` takes the module of the copy:

.. code-block:: diff

   -RTLIL::CaseRule *cs = new RTLIL::CaseRule;
   +RTLIL::CaseRule *cs = new RTLIL::CaseRule(module);

.. code-block:: diff

   -RTLIL::SwitchRule *sw = other_sw->clone();
   +RTLIL::SwitchRule *sw = other_sw->clone(module);

A ``SrcRef`` is valid only in its own ``Design``. ``Module::clone(Design *)``
re-interns source locations into the target design; elsewhere, use
``SrcPool::copy_from``:

.. code-block:: cpp

   dst->set_src(dst_design->srcs().copy_from(src_design->srcs(), src->src()));

Python helpers
^^^^^^^^^^^^^^

``pyosys`` exposes ``SrcRef`` as an opaque handle: ``SrcRef()`` and
``SrcRef.Null`` are the null handle, handles compare with ``==`` and can't be
hashed. ``src()``, ``set_src()`` and ``has_src()`` are available on every
object that has attributes. ``srcs()`` on ``Design``, ``Module``, ``Wire``,
``Memory``, ``Cell`` and ``Process`` returns the design's pool, which offers
``add_parsed``, ``merge``, ``str`` and ``locations``, which returns the
locations of a set as a list of strings. Python has no structured
way to build locations yet, so locations are created from strings with
``add_parsed``.

.. code-block:: diff

   -cell.set_src_attribute("top.v:3.5-3.9")
   +cell.set_src(design.srcs().add_parsed("top.v:3.5-3.9"))

.. code-block:: diff

   -src = cell.get_src_attribute()
   +src = cell.srcs().str(cell.src())

.. code-block:: diff

   -module.addAnd("\\and", a, b, y, src=cell.get_src_attribute())
   +module.addAnd("\\and", a, b, y, src=cell.src())

``Design.transfer_metadata`` and ``Design.absorb_metadata`` work as in C++.
``CaseRule`` and ``SwitchRule`` take their module as constructor argument.

RTLIL
^^^^^

`write_rtlil` refers to source locations instead of spelling them out. A
single location is written as ``@<twine>``, a reference into the ``twines``
section. A set of several locations is written as ``$<set>``, a reference
into a ``srcs`` section of the ``metadata`` block, with one ``set <set> <twine>...`` line per set:

.. code-block:: text

   metadata
     srcs
       set 0 1055 1056
     end
   end
   ...
     attribute \src "$0"  # top.v:3.5-3.9|top.v:4.5-4.9
     attribute \src "@1055"  # top.v:3.5-3.9

`read_rtlil` still accepts plain location strings, so older RTLIL files can
be read in. :yoscrypt:`write_rtlil -readable` writes plain strings for older Yosys
versions.
