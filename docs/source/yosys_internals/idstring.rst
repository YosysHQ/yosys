IdString
--------

Design
~~~~~~

String interning is a practice that deduplicates strings held in memory.
An integer then exactly represents a unique string. This also allows string
comparison to be replaced with integer comparison, which is faster.

For performance, memory efficiency, and future parallelism,
``IdString`` is an index into a per-``Design`` ``TwinePool``, which
deduplicates prefixes.

The killer feature is that it allows you to construct a new ``IdString`` by
appending a suffix to an existing ``IdString`` without copying its contents:

.. code-block:: cpp
   :caption: Example suffix node construction
   :name: idstring_suffix

   Wire *enable = module->addWire(TwineSpec::Suffix{cell->name, "_EN"}, 1);

A ``TwinePool`` holds a slab of ``TwineNode``\ s with free-list
bump allocation by inheriting from ``HashConsPool`` backed by
an ``std::deque``.
``HashConsPool`` provides deduplicating storage indexed by content hash.
``IdString``, being an interned string, is hashed as the underlying string.

``TwineSpec`` models an uninterned temporary twine node,
``TwineNode`` models an interned one.
``IdString`` then is an index into the vector
of ``TwineNode``\ s inside a ``TwinePool``.
More concretely, it is 32-bit, offset, and publicity-tagged.
The offset allows it to represent compilation-time allocated identifiers
in ``kernel/constids.inc``. Tagging implements "publicity", which historically
was determined by the first character being ``$`` or ``\``,
by stealing the top bit of the integer.
User-specified names coming in from design sources are public,
while Yosys-created names are private.

``TwineNode`` uses ``SmallString`` to store small strings inline and larger
ones behind a pointer. This keeps its own size at 24 bytes.
``AutoSuffix`` is a ``TwineSpec`` variant produced by ``NEW_ID``
and ``NEW_ID_SUFFIX`` macros. These are ``TwineSpec``s which skip string hashing
on the constant per-callsite prefix when repeatedly interned
and benefit from the ``SmallString`` implementation greatly to represent
the per-use incremented autoidx integer suffix.

Garbage collection traces a ``Design`` in parallel.

Migration from globally interned IdStrings
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

C++ core change
^^^^^^^^^^^^^^^

``IdString`` <-> string conversion now requires accessing a per-``Design``
``TwinePool``, accessible with ``design->twines()``, ``module->twines()``,
``wire->twines()``, ``cell->twines()``, ``memory->twines()``,
``process->twines()``

.. code-block:: diff

   -IdString id = "hello";
   +IdString id = design->twines().add("\\hello");

.. code-block:: diff

   -void thing(IdString id) {
   -    std::string s = id;
   -    log("%s\n", id);
   +void thing(Design* design, IdString id) {
   +    std::string s = design->twines().str(id);
   +    log("%s\n", s);
   // ...
   }

C++ helpers
^^^^^^^^^^^

When passing an IdString around that should then be stringified/printed or
assigned from string, you can use a ``PooledName`` which is effectively this but
with lots of convenient methods:

.. code-block:: cpp

   class PooledName { const TwinePool *pool_; IdString id_; }

so that you can

.. code-block:: diff

   -void foo(IdString name) {
   +void foo(PooledName name) {
       log("%s\n", name);
   }

   for (IdString name : names)
   -    foo(name);
   +    foo({design, name});

   // This then works without a change, since Cell::name
   // can magically convert to PooledName
   for (Cell* cell : cells)
       foo(cell->name);

In ``name`` fields on RTLIL objects and in ``Cell::type``, a ``Design*`` is
contextually available, so those fields are magically wrapping an IdString for
read access. That means you don't need a change here:

.. code-block:: cpp

   log("Cell type %s, cell name %s\n", cell->type, cell->name);

but not for write access, so you still have to do this:

.. code-block:: diff

   -cell->type = "\\asdfghjk";
   +cell->type = design->twines().add("\\asdfghjk");

Checking the first character of an ``IdString`` for publicity can now get
expensive. Do this instead:

.. code-block:: diff

   -if (wire->name[0] == '$')
   +if (!wire->name.isPublic())

``ID(id)`` now accepts only names in ``kernel/constids.inc``

.. code-block:: diff

   -auto w = miter_module->addWire(ID(asdfghjk));
   +auto w = miter_module->addWire("\\asdfghjk");

``IdString`` is valid only in its own ``Design``: cross-design use requires
``TwinePool::copy_from``, ``TwinePool::find_from``, ``Module::clone(Design *)``,
``RTLIL::copy_attr_dict``

``RTLIL::sort_by_id_str`` takes a ``TwinePool`` reference. This is a good time
to rethink whether you really want to sort stuff by string contents!

.. code-block:: diff

   -modules_.sort(sort_by_id_str());
   +modules_.sort(sort_by_id_str(design->twines()));

``NEW_ID``, ``NEW_ID_SUFFIX(suffix)`` change type from ``IdString`` to
``TwineSpec``.

But as long as you use them in the construction of RTLIL objects, magic happens:

.. code-block:: cpp

   SigSpec s = module->And(NEW_ID, lhs, rhs);

``RTLIL::unescape_id(IdString)`` and ``log_id`` have been removed, together with
other things that have relied on the old design.

Python helpers
^^^^^^^^^^^^^^

``pyosys`` lies to you - ``PooledName`` is what you're actually getting when you
get an ``IdString`` in Python. This is because we expect Python users to value
convenience and simplicity more than unnecessary bytes here. This is different
from what we need for our core optimization passes in C++.

Strings still work as names in methods of ``Design``, ``Module``, ``Cell``,
``Wire``, ``Memory`` and ``Process``, and as keys of their ``attributes``,
``parameters``, ``parameter_default_values``, ``connections_``, ``wires_``,
``cells_``, ``memories``, ``processes`` and ``modules_``, since those know their
design.

Elsewhere only static names (``"\\A"``, ``"$add"``) convert from strings. You
may otherwise need to get an ``IdString`` from the design:

.. code-block:: diff

   my_idict = ys.IdstringIdict()
   -my_idict("\\hello")
   -print(my_idict[0])
   +my_idict(design.id_add("\\hello"))
   +print(design.str(my_idict[0]))

Use ``id_find`` instead of ``id_add`` to only look a name up, it returns
``None`` if absent:

.. code-block:: diff

   -sel.selected_module("\\top")
   +sel.selected_module(design.id_find("\\top"))

``connections_``, ``wires_``, ``cells_``, ``memories``, ``processes`` and
``modules_`` can't be assigned as a whole anymore, use methods instead:

.. code-block:: diff

   -cell.connections_ = {"\\A": sig}
   +cell.setPort("\\A", sig)

Using a name after its design was deleted now raises ``RuntimeError``, so
convert it with ``str()`` while the design is still alive if you want that.

RTLIL
^^^^^

There is a new ``twines`` section in the RTLIL textual format. Older RTLIL
versions can still be read in, but older Yosys versions won't be able to read
this format.

To write out RTLIL in a format compatible with older
Yosys versions, use ``write_rtlil -readable``. This will discards only
prefix node structure, not string content. To remove human-readable comments
to save file size, use ``write_rtlil -small``.
