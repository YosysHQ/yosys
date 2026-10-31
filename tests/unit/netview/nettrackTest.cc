#include "netviewHelpers.h"

#include "kernel/nettrack.h"

YOSYS_NAMESPACE_BEGIN

using NetTrackTest = NetViewTest;

// The view after passes, the old view is retired
static std::unique_ptr<NetView> nextView(NetView &view, Design *design)
{
	view.retire();
	std::unique_ptr<NetView> next = std::make_unique<NetView>();
	next->build(design);
	return next;
}

TEST_F(NetTrackTest, anchorFindsEachFoundObject)
{
	ensurePasses();
	NetView view;
	view.build(d);
	NetTracker tracker;
	TrackedRef outer{TrackedRef::Kind::Instance}, inner{TrackedRef::Kind::Instance};
	outer.instances = {topChild(view, u_inv0), topChild(view, u_inv2)};
	inner.instances = {view.instance(i1, topChild(view, u_sub)), view.instance(i2, topChild(view, u_sub))};
	tracker.checkpoint(view, {&outer, &inner}, TrackMode::AnchorsOnly);
	Pass::call(d, "flatten");
	std::unique_ptr<NetView> next = nextView(view, d);
	tracker.resolve(*next, {&outer, &inner});
	std::vector<const Netlist::Instance *> outer_cells = {topChild(*next, u_inv0), topChild(*next, u_inv2)};
	std::vector<const Netlist::Instance *> inner_cells = {topChild(*next, top->cell("\\u_sub.i1")), topChild(*next, top->cell("\\u_sub.i2"))};
	for (std::vector<const Netlist::Instance *> *cells : {&outer.instances, &inner.instances, &outer_cells, &inner_cells})
		std::sort(cells->begin(), cells->end());
	EXPECT_EQ(outer.instances, outer_cells);
	EXPECT_EQ(inner.instances, inner_cells);
}

TEST_F(NetTrackTest, resolveTakesItsOwnOccurrence)
{
	Cell *u_sub2 = top->addCell("\\u_sub2", "\\sub");
	u_sub2->setPort(ID(a), in);
	NetView view;
	view.build(d);
	NetTracker tracker;
	TrackedRef ref{TrackedRef::Kind::Pin};
	ref.pins = {view.instance(i1, topChild(view, u_sub2))->pins[0]};
	tracker.checkpoint(view, {&ref}, TrackMode::AnchorsOnly);
	std::unique_ptr<NetView> next = nextView(view, d);
	tracker.resolve(*next, {&ref});
	ASSERT_EQ(ref.pins.size(), 1u);
	EXPECT_EQ(ref.pins[0]->inst->parent, topChild(*next, u_sub2));
	EXPECT_EQ(ref.result.own_pins, ref.pins);
	top->rename(u_sub2, "\\u_other");
	std::unique_ptr<NetView> last = nextView(*next, d);
	tracker.resolve(*last, {&ref});
	ASSERT_EQ(ref.pins.size(), 1u);
	EXPECT_EQ(ref.pins[0]->inst->parent, topChild(*last, u_sub2));
}

TEST_F(NetTrackTest, flattenCopyOfAKeptCellKeepsItsPath)
{
	ensurePasses();
	sub->set_bool_attribute(ID::keep_hierarchy);
	Module *mid = d->addModule("\\mid");
	Wire *mid_a = mid->addWire(ID(a));
	mid_a->port_input = true;
	mid->fixup_ports();
	mid->addCell("\\s", "\\sub")->setPort(ID(a), mid_a);
	Cell *m1 = top->addCell("\\m1", "\\mid");
	m1->setPort(ID(a), in);
	top->addCell("\\m2", "\\mid")->setPort(ID(a), in);
	NetView view;
	view.build(d);
	NetTracker tracker;
	TrackedRef ref{TrackedRef::Kind::Pin};
	ref.pins = {view.instance(i1, view.instance(mid->cell("\\s"), topChild(view, m1)))->pins[0]};
	tracker.checkpoint(view, {&ref}, TrackMode::AnchorsOnly);
	Pass::call(d, "flatten");
	std::unique_ptr<NetView> next = nextView(view, d);
	tracker.resolve(*next, {&ref});
	ASSERT_EQ(ref.pins.size(), 1u);
	EXPECT_EQ(ref.pins[0]->inst->parent, topChild(*next, top->cell("\\m1.s")));
}

// splitnets drops the anchors of the port wire, the port name finds the pin
TEST_F(NetTrackTest, topPortFindsItsPinByName)
{
	NetView view;
	view.build(d);
	NetTracker tracker;
	TrackedRef port{TrackedRef::Kind::TopPort};
	port.pins = {view.top()->findPin("q", 1)};
	tracker.checkpoint(view, {&port}, TrackMode::AnchorsOnly);
	q->attributes.clear();
	std::unique_ptr<NetView> next = nextView(view, d);
	tracker.resolve(*next, {&port});
	EXPECT_EQ(port.pins, std::vector<const Netlist::Pin *>{next->top()->findPin("q", 1)});
}

// After clear, resolve finds nothing
TEST_F(NetTrackTest, clearForgetsTheAnchors)
{
	NetView view;
	view.build(d);
	NetTracker tracker;
	TrackedRef cell{TrackedRef::Kind::Instance};
	cell.instances = {topChild(view, u_inv2)};
	tracker.checkpoint(view, {&cell}, TrackMode::AnchorsOnly);
	tracker.clear(d);
	std::unique_ptr<NetView> next = nextView(view, d);
	tracker.resolve(*next, {&cell});
	EXPECT_TRUE(cell.instances.empty());
}

using NetTrackDeathTest = NetTrackTest;

// The delete of an unconnected cell fires no monitor event
TEST_F(NetTrackDeathTest, checkpointRefusesAStaleView)
{
	Cell *u_spare = top->addCell("\\u_spare", ID(INV));
	NetView view;
	view.build(d);
	NetTracker tracker;
	TrackedRef ref{TrackedRef::Kind::Instance};
	ref.instances = {topChild(view, u_spare)};
	top->remove(u_spare);
	EXPECT_TRUE(view.upToDate());
	// log_assert exits with 1, a write to the freed cell is no exit or a signal
	EXPECT_EXIT(tracker.checkpoint(view, {&ref}, TrackMode::AnchorsOnly), ::testing::ExitedWithCode(1), "");
}

YOSYS_NAMESPACE_END
