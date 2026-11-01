#include "netviewHelpers.h"

#include "kernel/nettrack.h"
#include "kernel/sigtools.h"

YOSYS_NAMESPACE_BEGIN

using NetProtectTest = NetViewTest;

// The view after passes with the Barrier instances of the tracker, the old view is cleared
static std::unique_ptr<NetView> nextView(NetView &view, const NetTracker &tracker, Design *design)
{
	view.clear();
	pool<const Cell *> barriers = tracker.barrierInstances(design);
	std::unique_ptr<NetView> next = std::make_unique<NetView>();
	next->build(design, {nullptr, &barriers});
	return next;
}

// The $barrier cells of a module
static std::vector<Cell *> barriersOf(Module *module)
{
	std::vector<Cell *> barriers;
	for (Cell *cell : module->cells()) {
		if (cell->type == ID($barrier))
			barriers.push_back(cell);
	}
	return barriers;
}

static Cell *addBidiCell(Design *design, Module *parent, const SigSpec &signal)
{
	Module *bidi = design->addModule("\\BIDI");
	Wire *io = bidi->addWire("\\IO");
	io->port_input = true;
	io->port_output = true;
	bidi->fixup_ports();
	bidi->set_bool_attribute(ID::blackbox);
	Cell *b = parent->addCell("\\b", "\\BIDI");
	b->setPort("\\IO", signal);
	return b;
}

using Pins = std::vector<const Netlist::Pin *>;

static Pins sortedPins(Pins pins)
{
	std::sort(pins.begin(), pins.end());
	return pins;
}

static TrackedRef pinRef(const Pins &pins, TrackedRef::Kind kind = TrackedRef::Kind::Pin)
{
	TrackedRef ref{kind};
	ref.pins = pins;
	return ref;
}

struct TrackedView {
	Design *design;
	std::unique_ptr<NetView> view = std::make_unique<NetView>();
	NetTracker tracker;

	explicit TrackedView(Design *design) : design(design) { view->build(design); }
	Netlist::Instance *child(const Cell *cell) const { return topChild(*view, cell); }
	void checkpoint(const std::vector<TrackedRef *> &refs) { tracker.checkpoint(*view, refs, TrackMode::Barriers); }
	// The view after a pass, the refs resolved in it
	void next(const std::vector<TrackedRef *> &refs)
	{
		view = nextView(*view, tracker, design);
		tracker.resolve(*view, refs);
	}
};

TEST_F(NetProtectTest, clockPinKeepsABarrierInstance)
{
	NetView view;
	view.build(d);
	NetTracker tracker;
	TrackedRef ref{TrackedRef::Kind::Pin};
	ref.hints.keep_as_instance = true;
	ref.pins = {topChild(view, u_sub)->pins[0]};
	tracker.checkpoint(view, {&ref}, TrackMode::Barriers);
	view.recheck();
	EXPECT_FALSE(view.upToDate());
	std::unique_ptr<NetView> next = nextView(view, tracker, d);
	tracker.resolve(*next, {&ref});
	ASSERT_EQ(ref.result.barrier_a_pins.size(), 1u);
	ASSERT_EQ(ref.result.barrier_y_pins.size(), 1u);
	const Netlist::Pin *a = ref.result.barrier_a_pins[0];
	const Netlist::Pin *y = ref.result.barrier_y_pins[0];
	EXPECT_TRUE(a->inst->kind == Netlist::Instance::Kind::Barrier);
	EXPECT_EQ(a->dir(), Netlist::PortDir::Input);
	EXPECT_EQ(a->net, topChild(*next, u_sub)->pins[0]->inner);
	EXPECT_EQ(y->net, next->instance(i1, topChild(*next, u_sub))->pins[0]->net);
	EXPECT_NE(a->net, y->net);
	ASSERT_EQ(next->nets(a->inst).size(), 1u);
	EXPECT_EQ(a->inner, y->inner);
	std::vector<const Netlist::Pin *> loads = {next->instance(i1, topChild(*next, u_sub))->pins[0],
						   next->instance(i2, topChild(*next, u_sub))->pins[0]};
	EXPECT_EQ(sortedPins(ref.pins), sortedPins(loads));
	EXPECT_TRUE(ref.result.flattened_hier_pin);
	TrackedRef on_barrier{TrackedRef::Kind::Pin};
	on_barrier.pins = {a};
	tracker.checkpoint(*next, {&on_barrier}, TrackMode::AnchorsOnly);
	EXPECT_TRUE(on_barrier.origin.on_barrier_instance);
}

TEST_F(NetProtectTest, unprotectKeepsTheAnchors)
{
	ensurePasses();
	NetView view;
	view.build(d);
	NetTracker tracker;
	TrackedRef cell{TrackedRef::Kind::Instance};
	cell.instances = {topChild(view, u_inv2)};
	tracker.checkpoint(view, {&cell}, TrackMode::Barriers);
	EXPECT_TRUE(u_inv2->get_bool_attribute(ID::keep));
	EXPECT_EQ(barriersOf(top).size(), 2u); // a barrier at each pin
	tracker.unprotect(d);
	EXPECT_FALSE(u_inv2->has_attribute(ID::keep));
	EXPECT_EQ(top->cells().size(), 3u);
	view.recheck();
	EXPECT_FALSE(view.upToDate());
	std::unique_ptr<NetView> next = nextView(view, tracker, d);
	tracker.resolve(*next, {&cell});
	EXPECT_EQ(cell.instances, std::vector<const Netlist::Instance *>{topChild(*next, u_inv2)});
}

// rename -hide gives the barriers new names, unprotect finds them by their id
TEST_F(NetProtectTest, removedCellKeepsItsLoads)
{
	NetView view;
	view.build(d);
	NetTracker tracker;
	TrackedRef cell{TrackedRef::Kind::Instance};
	cell.instances = {topChild(view, u_inv2)};
	tracker.checkpoint(view, {&cell}, TrackMode::Barriers);
	// a pass makes the cell a wire
	top->connect(u_inv2->getPort(ID(Y)), u_inv2->getPort(ID(A)));
	top->remove(u_inv2);
	std::unique_ptr<NetView> next = nextView(view, tracker, d);
	tracker.resolve(*next, {&cell});
	EXPECT_TRUE(cell.instances.empty());
	EXPECT_EQ(cell.result.loads_beyond, std::vector<const Netlist::Pin *>{next->top()->findPin("out", 0)});
	EXPECT_TRUE(cell.removedButLoadsKept());
}

// The name finds no port, the barrier finds it by its signal
TEST_F(NetProtectTest, netBarrierFindsTheNetOfItsScope)
{
	NetView view;
	view.build(d);
	NetTracker tracker;
	TrackedRef net{TrackedRef::Kind::Net};
	net.nets = {topChild(view, u_inv2)->pins[0]->net};
	tracker.checkpoint(view, {&net}, TrackMode::Barriers);
	// splitnets drops the anchors of the wire
	p->attributes.clear();
	std::unique_ptr<NetView> next = nextView(view, tracker, d);
	tracker.resolve(*next, {&net});
	EXPECT_EQ(net.nets, std::vector<const Netlist::Net *>{topChild(*next, u_inv2)->pins[0]->net});
}

TEST_F(NetProtectTest, loopOfNewBuffersEnds)
{
	NetView view;
	view.build(d);
	NetTracker tracker;
	TrackedRef ref{TrackedRef::Kind::Pin};
	ref.pins = {topChild(view, u_inv2)->pins[0]};
	tracker.checkpoint(view, {&ref}, TrackMode::Barriers);
	// a pass puts a loop of buffers on the cut wire
	SigBit cut = u_inv2->getPort(ID(A));
	Wire *b = top->addWire("\\b");
	Cell *b1 = top->addCell("$b1", ID($_BUF_));
	b1->setPort(ID::A, cut);
	b1->setPort(ID::Y, b);
	Cell *b2 = top->addCell("$b2", ID($_BUF_));
	b2->setPort(ID::A, b);
	b2->setPort(ID::Y, cut);
	std::unique_ptr<NetView> next = nextView(view, tracker, d);
	tracker.resolve(*next, {&ref});
	EXPECT_EQ(ref.pins, std::vector<const Netlist::Pin *>{topChild(*next, u_inv2)->pins[0]});
}

TEST_F(NetProtectTest, ringOfNewBuffersOnAPartEnds)
{
	Wire *n = top->addWire("\\n");
	top->connect(n, d0);
	NetView view;
	view.build(d);
	NetTracker tracker;
	TrackedRef net{TrackedRef::Kind::Net};
	net.nets = {topChild(view, u_inv0)->pins[1]->net};
	tracker.checkpoint(view, {&net}, TrackMode::Barriers);
	// n gets its own driver, a ring of new buffers drives d0
	top->new_connections({{tie, State::S0}});
	Cell *inv = top->addCell("$inv", ID(INV));
	inv->setPort(ID(A), in);
	inv->setPort(ID(Y), n);
	Wire *x = top->addWire("\\x");
	Cell *r1 = top->addCell("$r1", ID($_BUF_));
	r1->setPort(ID::A, d0);
	r1->setPort(ID::Y, x);
	Cell *r2 = top->addCell("$r2", ID($_BUF_));
	r2->setPort(ID::A, x);
	r2->setPort(ID::Y, d0);
	std::unique_ptr<NetView> next = nextView(view, tracker, d);
	tracker.resolve(*next, {&net});
	EXPECT_FALSE(net.nets.empty());
}

// insbuf puts a buffer between a top input and its barrier, a pass renames the port
TEST_F(NetProtectTest, portBarrierPassesANewBuffer)
{
	NetView view;
	view.build(d);
	NetTracker tracker;
	TrackedRef port{TrackedRef::Kind::TopPort};
	port.pins = {view.top()->findPin("q", 1)};
	tracker.checkpoint(view, {&port}, TrackMode::Barriers);
	Wire *w = top->addWire("\\w");
	Cell *buf = top->addCell("$buf", ID($_BUF_));
	buf->setPort(ID::A, SigBit(q, 1));
	buf->setPort(ID::Y, w);
	ASSERT_EQ(barriersOf(top).size(), 1u);
	barriersOf(top)[0]->setPort(ID::A, w);
	q->attributes.clear();
	top->rename(q, "\\q_renamed");
	top->fixup_ports();
	std::unique_ptr<NetView> next = nextView(view, tracker, d);
	tracker.resolve(*next, {&port});
	EXPECT_EQ(port.pins, std::vector<const Netlist::Pin *>{next->top()->findPin("q_renamed", 1)});
}

TEST_F(NetProtectTest, newBarriersSkipIdsInUse)
{
	NetView view;
	view.build(d);
	TrackedRef in_sub{TrackedRef::Kind::Pin}, in_top{TrackedRef::Kind::Pin}, again{TrackedRef::Kind::Pin};
	in_sub.pins = {view.instance(i1, topChild(view, u_sub))->pins[0]};
	IdString id_attr;
	std::unique_ptr<NetView> next;
	{
		NetTracker first;
		first.checkpoint(view, {&in_sub}, TrackMode::Barriers);
		id_attr = d->twines().find("\\netview_anchor");
		Cell *read_back = barriersOf(sub)[0];
		read_back->attributes[id_attr] = Const(read_back->attributes.at(id_attr).as_int() + 1);
		next = nextView(view, first, d);
	}
	NetTracker second;
	in_top.pins = {topChild(*next, u_inv2)->pins[0]};
	again.pins = {topChild(*next, u_inv0)->pins[0]};
	second.checkpoint(*next, {&in_top, &again}, TrackMode::Barriers);
	std::vector<Cell *> barriers = barriersOf(top);
	ASSERT_EQ(barriers.size(), 2u);
	ASSERT_EQ(barriersOf(sub).size(), 1u);
	barriers.push_back(barriersOf(sub)[0]);
	pool<int> ids;
	for (Cell *barrier : barriers)
		ids.insert(barrier->attributes.at(id_attr).as_int());
	EXPECT_EQ(ids.size(), 3u);
}

TEST_F(NetProtectTest, inoutPinIsALoadBeyondABarrier)
{
	Cell *b = addBidiCell(d, top, d0);
	NetView view;
	view.build(d);
	NetTracker tracker;
	TrackedRef ref{TrackedRef::Kind::Instance};
	ref.instances = {topChild(view, u_inv0)};
	tracker.checkpoint(view, {&ref}, TrackMode::Barriers);
	std::unique_ptr<NetView> next = nextView(view, tracker, d);
	tracker.resolve(*next, {&ref});
	const Netlist::Pin *b_io = topChild(*next, b)->pins[0];
	std::vector<const Netlist::Pin *> &loads = ref.result.loads_beyond;
	EXPECT_NE(std::find(loads.begin(), loads.end(), b_io), loads.end());
	EXPECT_NE(std::find(loads.begin(), loads.end(), next->instance(i1, topChild(*next, u_sub))->pins[0]), loads.end());
}

TEST_F(NetProtectTest, inoutPinsKeepTheirCells)
{
	ensurePasses();
	Cell *b = addBidiCell(d, top, d0);
	Module *m = d->addModule("\\m");
	Wire *io = m->addWire("\\io");
	io->port_input = io->port_output = true;
	m->fixup_ports();
	m->addCell("\\b", "\\BIDI")->setPort("\\IO", io);
	top->addCell("\\u_m", "\\m")->setPort("\\io", d0);
	TrackedView t(d);
	TrackedRef ref = pinRef({t.child(b)->pins[0], t.child(top->cell("\\u_m"))->pins[0]});
	t.checkpoint({&ref});
	EXPECT_TRUE(barriersOf(top).empty());
	EXPECT_EQ(b->getPort(d->twines().find("\\IO")), SigSpec(d0));
	EXPECT_TRUE(b->get_bool_attribute(ID::keep));
	Pass::call(d, "flatten");
	ASSERT_EQ(top->cell("\\u_m")->type, m->name); // a flattened u_m leaves a $scopeinfo cell u_m
	t.next({&ref});
	EXPECT_EQ(sortedPins(ref.pins), sortedPins({t.child(b)->pins[0], t.child(top->cell("\\u_m"))->pins[0]}));
}

TEST_F(NetProtectTest, pinRefKeepsEachOfItsPins)
{
	Cell *u_c = top->addCell("\\u_c", ID(INV));
	u_c->setPort(ID(A), State::S0);
	TrackedView t(d);
	TrackedRef ref = pinRef({t.child(u_c)->pins[0], t.child(u_inv2)->pins[0], t.child(u_sub)->findPin("a", 0)});
	t.checkpoint({&ref});
	t.next({&ref});
	EXPECT_EQ(sortedPins(ref.pins), sortedPins({t.child(u_c)->pins[0], t.child(u_inv2)->pins[0], t.child(u_sub)->findPin("a", 0)}));
	EXPECT_FALSE(ref.isBehindNewLogic());
	EXPECT_FALSE(ref.result.flattened_hier_pin);
}

TEST_F(NetProtectTest, renamedPortOfAFeedthroughKeepsItsDirection)
{
	ensurePasses();
	Module *feed = d->addModule("\\feed");
	Wire *feed_b = feed->addWire("\\b");
	feed_b->port_output = true;
	Wire *feed_d = feed->addWire("\\d", 2);
	feed_d->port_input = true;
	feed->fixup_ports();
	feed->connect(feed_b, SigBit(feed_d, 1));
	feed->addCell("\\g", ID(INV))->setPort(ID(A), SigBit(feed_d, 1));
	Cell *u_f = top->addCell("\\u_f", "\\feed");
	u_f->setPort("\\d", SigSpec(q).extract(0, 2));
	TrackedView t(d);
	TrackedRef ref = pinRef({t.child(u_f)->findPin("d", 1)});
	t.checkpoint({&ref});
	Pass::call(d, "splitnets -ports feed");
	t.next({&ref});
	ASSERT_EQ(ref.pins.size(), 1u);
	EXPECT_EQ(ref.pins[0]->inst, t.child(u_f));
	EXPECT_EQ(ref.pins[0]->dir(), Netlist::PortDir::Input);
}

// u_inv2 keeps its anchor and ports, it has no port renames. A pass maps g(A[1:0], Y) to G2(I[1:0], Y) with the bits
// of A swapped, the renames of g hold the old and the new bit
TEST_F(NetProtectTest, pinRefFindsTopPins)
{
	Wire *o = top->addWire("\\o");
	o->port_output = true;
	top->fixup_ports();
	top->connect(o, State::S0);
	TrackedView t(d);
	TrackedRef ref = pinRef({t.view->top()->findPin("in", 0), t.view->top()->findPin("o", 0), t.child(u_inv0)->pins[0]});
	t.checkpoint({&ref});
	top->rename(in, "\\in2");
	top->rename(out, "\\in");
	top->fixup_ports();
	t.next({&ref});
	EXPECT_EQ(sortedPins(ref.pins), sortedPins({t.view->top()->findPin("in2", 0), t.view->top()->findPin("o", 0), t.child(u_inv0)->pins[0]}));
}

TEST_F(NetProtectTest, refsOnFlattenCopiesOfABarrierKeepOnlyThem)
{
	ensurePasses();
	top->addCell("\\u_sub2", "\\sub")->setPort(ID(a), in);
	top->addCell("\\u_sub3", "\\sub")->setPort(ID(a), in);
	TrackedView t(d);
	TrackedRef pin = pinRef({t.child(u_sub)->pins[0]});
	pin.hints.keep_as_instance = true;
	t.checkpoint({&pin});
	Pass::call(d, "flatten");
	t.next({});
	std::vector<Cell *> copies = barriersOf(top);
	ASSERT_EQ(copies.size(), 3u);
	TrackedRef on_copy = pinRef({t.child(copies[0])->findPin("A", 0)}), cell{TrackedRef::Kind::Instance};
	cell.instances = {t.child(copies[1])};
	t.checkpoint({&on_copy, &cell});
	EXPECT_EQ(barriersOf(top).size(), 2u);
}

// A pass buffers the feedthrough o2 = in. The wire anchor on o2 is no lost name, the ref of in keeps in only
TEST_F(NetProtectTest, flattenedOutputPinKeepsItsLoadsBeyond)
{
	ensurePasses();
	TrackedView t(d);
	TrackedRef ref = pinRef({t.child(u_sub)->findPin("y", 0)});
	t.checkpoint({&ref});
	Pass::call(d, "flatten");
	t.next({&ref});
	t.checkpoint({&ref});
	t.next({&ref});
	EXPECT_EQ(ref.result.loads_beyond, Pins{t.child(u_inv2)->pins[0]});
}

YOSYS_NAMESPACE_END
