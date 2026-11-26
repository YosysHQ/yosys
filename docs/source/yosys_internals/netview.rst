NetView and NetTracker
----------------------

Design
~~~~~~

Many passes rename, merge, flatten or remove cells and wires. A tool that
keeps its own data about netlist objects, such as the timing constraints of
the OpenSTA plugin `opensta_net <https://github.com/YosysHQ/opensta_net>`_,
has to find those objects again after each pass.

``NetView`` (:file:`kernel/netview/netview.h`) is a read-only, bit-level
snapshot of a design with its hierarchy unfolded. The top module and every cell
below it become an ``Instance``, with a ``Pin`` per port bit and a ``Net`` per
signal bit that reaches a pin. A module used twice gets two copies of
everything. An instance is the top, a scope (a cell of a module that is not a
blackbox or whitebox) or a leaf (any other cell). The records live in the
``Netlist`` namespace. Instance ids count from 0 (the top), pin and net ids
from 1, so pin ``n`` is ``pins()[n - 1]``.

The view looks through `$connect` and `$barrier` cells, and gives them,
`$input_port` and `$scopeinfo` no instance. Leaf ports come from the
``Netlist::CellLibrary`` you pass to the constructor, else from a blackbox
module, else from the Yosys cell types. The view does not follow the design.
``upToDate()`` turns false when the module list, the top, or the cells, wires
or connections of a module in the view change. It misses cell parameters and
attributes. The RTLIL pointers in the records are only safe while it is true.
The caller checks it, and ``checkpoint()`` asserts it.

``NetTracker`` (:file:`kernel/netview/nettrack.h`) finds the objects of an old
view again in a new one. ``checkpoint()`` writes a ``netview_ref`` id attribute
on each object you want to follow and puts `$barrier` cells at its pins, so
optimizations cannot merge or remove it. After your passes,
``resolve()`` reads the ids back in a new view and tells you what each object
turned into.

Usage
~~~~~

The design needs a top module and no processes, so run `hierarchy -top` and
`proc` first. ``NetView::buildable()`` tells you why a design has no view.
The constructor can still fail with ``log_cmd_error`` on a leaf type with no
known ports.

Put the objects you want to follow in a ``TrackedRef``. A ref holds pins,
instances or nets, one kind per ref, and never the top instance.

.. code-block:: cpp
   :caption: Follow the first pin of the top module through `flatten`

   NetTracker tracker;
   auto view = std::make_unique<NetView>(design);
   const Netlist::Pin *pin = &view->pins()[0];
   TrackedRef ref = {.kind = TrackedRef::Kind::Pin, .pins = {pin}};
   tracker.checkpoint(*view, {&ref});

   Pass::call(design, "flatten");

   view = std::make_unique<NetView>(design);
   tracker.resolve(*view, {&ref});
   if (ref.gone)
       log("lost the ref\n");

``checkpoint()`` needs an up-to-date view and keeps it up to date, so you can
go on using it.
``resolve()`` matches refs by position, so pass the same refs in the same
order. It never reads the old view, and you can call it again with a newer
one.

Make a new checkpoint after your own changes to the design, before the next
pass.

After ``resolve()``, a ref holds what its objects turned into:

- A pin with a barrier becomes the pins now on its side of the barrier.
- A pin of a scope that `flatten` removed becomes the leaf pins below it, the
  loads of an input or the drivers of an output. An output that also drove
  loads inside the scope is gone, and ``loads`` holds the loads outside.
- A cell that a pass split or replaced becomes the cells now between its old
  barriers. ``port_cuts`` lists the pins on each old port. A cell that kept
  its id stays the ref, unless a new cell that other logic feeds drives one of
  its old outputs, like a sibling of a ``_TECHMAP_REPLACE_`` cell. Then it is
  ``gone`` and becomes the cells between too, or stays the kept cell if no other
  cell is between. When cells remain, ``partial`` is set when a wire or a cell
  beside them drives an old output. A cell that only they feed, like an inverter
  after QN, and a tie cell do not count.
- A net below the top that is gone becomes the leaf pins of that net, so the
  ref turns into a pin ref.
- If nothing is left between the barriers of a gone pin or cell, for example
  because a pass turned a cell into a wire, ``loads`` holds the pins behind
  them. A cell with an inout pin gets none. The next ``checkpoint()`` anchors
  these for a pin ref.
- Else ``gone`` is set only if none of the objects were found.

Barriers
~~~~~~~~

Ids alone do not stop a pass from merging or removing an object. So
``checkpoint()`` puts a `$barrier` between each ref pin and its net, on
every pin of a leaf ref cell and at the leaf drivers of a ref net. Leaf ref
cells get ``keep`` and scope ref cells get ``keep_hierarchy``. So does a
scope with a private name above a ref, because `flatten` only keeps scope
names below public ones. Inout, constant and unconnected pins and top ports
get no barrier.

The view unfolds the hierarchy, so a ref names one instance, and only that
instance comes back from ``resolve()``. The barriers and keep attributes go
into the module though, which all its instances share. So the other instances
get them too and are optimized less. Run `flatten` or `uniquify` first if that
matters.

``unprotect()`` removes only the barriers, keep attributes and cut marks that
the tracker added. The ids and ``hdlname`` stay, so ``resolve()`` still finds
cells, leaf pins and nets. A scope pin with a barrier is anchored only by it
and gets lost. Call it before you write the design out.

Limits
~~~~~~

- Use one tracker per design, from one thread.
- If a pass copies a cell with its id and no copy stays at its old place in
  the hierarchy, ``resolve()`` cannot tell the copies apart. The cell is then
  ``gone``, and the ref becomes the cells between its barriers, if any.
- A copy of a cell that kept its attributes can be found in place of the
  deleted original.
- Without a barrier, a cell or wire is lost when a pass drops its attributes.
