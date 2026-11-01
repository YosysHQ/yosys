#include "netviewHelpers.h"

#include "kernel/nettrack.h"

YOSYS_NAMESPACE_BEGIN

using NetTrackTest = NetViewTest;

// The view after passes, the old view is cleared
static std::unique_ptr<NetView> nextView(NetView &view, Design *design)
{
	view.clear();
	std::unique_ptr<NetView> next = std::make_unique<NetView>();
	next->build(design);
	return next;
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

// design -load brings back the attributes of an earlier checkpoint
// design -load moves autoidx back, the loaded u_inv0 holds the anchor of the first checkpoint
using NetTrackDeathTest = NetTrackTest;

// The delete of an unconnected cell fires no monitor event
// Two trackers on one design remove the anchors, keeps and barriers of each other
YOSYS_NAMESPACE_END
