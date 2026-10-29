#include "netviewHelpers.h"

#include "kernel/nettrack.h"

YOSYS_NAMESPACE_BEGIN

using NetProtectTest = NetViewTest;

// The view after passes with the Barrier instances of the tracker, the old view is retired
static std::unique_ptr<NetView> nextView(NetView &view, const NetTracker &tracker, Design *design)
{
	view.retire();
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
	EXPECT_EQ(a->net, topChild(*next, u_sub)->pins[0]->term->net);
	EXPECT_EQ(y->net, next->instance(i1, topChild(*next, u_sub))->pins[0]->net);
	EXPECT_NE(a->net, y->net);
	ASSERT_EQ(next->nets(a->inst).size(), 1u);
	EXPECT_EQ(a->term->net, y->term->net);
	std::vector<const Netlist::Pin *> loads = {next->instance(i1, topChild(*next, u_sub))->pins[0],
						   next->instance(i2, topChild(*next, u_sub))->pins[0]};
	std::sort(loads.begin(), loads.end());
	EXPECT_EQ(ref.pins, loads);
	EXPECT_TRUE(ref.result.flattened_hier_pin);
	TrackedRef on_barrier{TrackedRef::Kind::Pin};
	on_barrier.pins = {a};
	tracker.checkpoint(*next, {&on_barrier}, TrackMode::AnchorsOnly);
	EXPECT_TRUE(on_barrier.origin.on_barrier_instance);
}

TEST_F(NetProtectTest, protectFindsAPinAfterFlatten)
{
	ensurePasses();
	NetView view;
	view.build(d);
	NetTracker tracker;
	TrackedRef ref{TrackedRef::Kind::Pin}, net{TrackedRef::Kind::Net};
	ref.pins = {view.instance(i1, topChild(view, u_sub))->pins[0]};
	net.nets = {topChild(view, u_inv0)->pins[0]->net};
	tracker.checkpoint(view, {&ref, &net}, TrackMode::Barriers);
	EXPECT_TRUE(view.upToDate());
	Pass::call(d, "flatten");
	Cell *old = top->cell("\\u_sub.i1");
	ASSERT_NE(old, nullptr);
	Cell *renewed = top->addCell("$renewed", ID(INV));
	renewed->setPort(ID(A), old->getPort(ID(A)));
	renewed->setPort(ID(Y), old->getPort(ID(Y)));
	top->remove(old);
	std::unique_ptr<NetView> next = nextView(view, tracker, d);
	tracker.resolve(*next, {&ref, &net});
	EXPECT_EQ(net.nets, std::vector<const Netlist::Net *>{topChild(*next, u_inv0)->pins[0]->net});
	ASSERT_EQ(ref.pins.size(), 1u);
	EXPECT_EQ(next->cell(ref.pins[0]->inst), renewed);
	EXPECT_EQ(ref.pins[0]->port().name, "A");
}

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
TEST_F(NetProtectTest, portBarrierFindsItsPortBySignal)
{
	NetView view;
	view.build(d);
	NetTracker tracker;
	TrackedRef port{TrackedRef::Kind::TopPort};
	port.pins = {view.top()->findPin("q", 1)};
	tracker.checkpoint(view, {&port}, TrackMode::Barriers);
	// abc9 puts a wire between the barrier and the port, splitnets drops the anchors, a pass renames the port
	Wire *w = top->addWire("\\w");
	top->connect(w, SigBit(q, 1));
	ASSERT_EQ(barriersOf(top).size(), 1u);
	barriersOf(top)[0]->setPort(ID::A, w);
	q->attributes.clear();
	top->rename(q, "\\q_renamed");
	top->fixup_ports();
	std::unique_ptr<NetView> next = nextView(view, tracker, d);
	tracker.resolve(*next, {&port});
	EXPECT_EQ(port.pins, std::vector<const Netlist::Pin *>{next->top()->findPin("q_renamed", 1)});
}

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

YOSYS_NAMESPACE_END
