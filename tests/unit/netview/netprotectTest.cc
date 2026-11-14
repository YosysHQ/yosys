#include "netviewHelpers.h"

#include "kernel/sigtools.h"

YOSYS_NAMESPACE_BEGIN

using NetProtectTest = NetViewTest;

// the $barrier cells of a module
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

TEST_F(NetProtectTest, unprotectKeepsTheAnchors)
{
	ensurePasses();
	TrackedView t(d);
	TrackedRef cell{.kind = TrackedRef::Kind::Instance, .instances = {t.child(u_inv2)}};
	TrackedRef pin = pinRef({t.child(u_inv2)->pins[0]});
	t.checkpoint({&cell, &pin});
	EXPECT_TRUE(u_inv2->get_bool_attribute(ID::keep));
	EXPECT_EQ(barriersOf(top).size(), 2u); // at the pin of the pin ref and at the output of the cell
	t.tracker.unprotect(d);
	EXPECT_FALSE(u_inv2->has_attribute(ID::keep));
	EXPECT_EQ(top->cells().size(), 3u);
	EXPECT_FALSE(t.view->upToDate());
	t.next({&cell, &pin});
	EXPECT_EQ(cell.instances, std::vector<const Netlist::Instance *>{t.child(u_inv2)});
}

TEST_F(NetProtectTest, cellThatBecameAWireGivesTheLoadsBehindIt)
{
	TrackedView t(d);
	TrackedRef cell{.kind = TrackedRef::Kind::Instance, .instances = {t.child(u_inv2)}};
	t.checkpoint({&cell});
	// a pass makes the cell a wire
	top->connect(u_inv2->getPort(ID(Y)), u_inv2->getPort(ID(A)));
	top->remove(u_inv2);
	t.next({&cell});
	EXPECT_TRUE(cell.instances.empty());
	EXPECT_TRUE(cell.pins.empty());
	EXPECT_EQ(cell.loads, std::vector<const Netlist::Pin *>{t.view->top()->findPin("out", 0)});
	EXPECT_EQ(cell.port_cuts.size(), 2u);
}

TEST_F(NetProtectTest, splitCellGivesTheCellsBetweenItsBarriers)
{
	TrackedView t(d);
	TrackedRef cell{.kind = TrackedRef::Kind::Instance, .instances = {t.child(u_inv2)}};
	t.checkpoint({&cell});
	// a pass maps the cell to two cells
	Wire *mid = top->addWire("\\mid");
	Cell *first = top->addCell("\\first", ID(INV));
	first->setPort(ID(A), u_inv2->getPort(ID(A)));
	first->setPort(ID(Y), mid);
	Cell *second = top->addCell("\\second", ID(INV));
	second->setPort(ID(A), mid);
	second->setPort(ID(Y), u_inv2->getPort(ID(Y)));
	top->remove(u_inv2);
	t.next({&cell});
	EXPECT_TRUE(cell.gone);
	std::vector<const Netlist::Instance *> between = {t.child(first), t.child(second)};
	std::sort(between.begin(), between.end());
	std::vector<const Netlist::Instance *> found = cell.instances;
	std::sort(found.begin(), found.end());
	EXPECT_EQ(found, between);
	EXPECT_TRUE(cell.loads.empty());
}

TEST_F(NetProtectTest, deletedCellGivesNoPins)
{
	TrackedView t(d);
	TrackedRef cell{.kind = TrackedRef::Kind::Instance, .instances = {t.child(u_inv2)}};
	t.checkpoint({&cell});
	top->remove(u_inv2);
	t.next({&cell});
	EXPECT_TRUE(cell.instances.empty());
	EXPECT_TRUE(cell.loads.empty());
}

// the wire lost its id, the driver barrier finds the net
TEST_F(NetProtectTest, netBarrierFindsTheNetOfItsScope)
{
	TrackedView t(d);
	TrackedRef net{.kind = TrackedRef::Kind::Net, .nets = {t.child(u_inv2)->pins[0]->net}};
	t.checkpoint({&net});
	// splitnets drops the anchors of the wire
	p->attributes.clear();
	t.next({&net});
	EXPECT_EQ(net.nets, std::vector<const Netlist::Net *>{t.child(u_inv2)->pins[0]->net});
}

// the driver is gone, the wire still names the net
TEST_F(NetProtectTest, netWireFindsTheNetWithNoDriver)
{
	TrackedView t(d);
	TrackedRef net{.kind = TrackedRef::Kind::Net, .nets = {t.child(u_sub)->pins[0]->net}};
	t.checkpoint({&net});
	top->remove(u_inv0);
	t.next({&net});
	EXPECT_EQ(net.nets, std::vector<const Netlist::Net *>{t.child(u_sub)->pins[0]->net});
}

// a pass copies the wire with its id, two wires with the id are twins
TEST_F(NetProtectTest, copiedNetWireIsATwin)
{
	TrackedView t(d);
	TrackedRef net{.kind = TrackedRef::Kind::Net, .nets = {t.child(u_sub)->pins[0]->net}};
	t.checkpoint({&net});
	top->remove(u_inv0);
	u_sub->setPort(ID(a), top->addWire(NEW_ID, d0));
	t.next({&net});
	EXPECT_TRUE(net.nets.empty());
}

TEST_F(NetProtectTest, newBarriersSkipIdsInUse)
{
	IdString id_attr;
	{
		TrackedView first(d);
		TrackedRef in_sub = pinRef({first.view->instance(i1, first.child(u_sub))->pins[0]});
		first.checkpoint({&in_sub});
		id_attr = d->twines().find("\\netview_ref");
		Cell *read_back = barriersOf(sub)[0];
		read_back->attributes[id_attr] = Const(read_back->attributes.at(id_attr).as_int() + 1000);
	}
	TrackedView second(d);
	TrackedRef in_top = pinRef({second.child(u_inv2)->pins[0]});
	TrackedRef again = pinRef({second.child(u_inv0)->pins[0]});
	second.checkpoint({&in_top, &again});
	std::vector<Cell *> barriers = barriersOf(top);
	ASSERT_EQ(barriers.size(), 2u);
	ASSERT_EQ(barriersOf(sub).size(), 1u);
	barriers.push_back(barriersOf(sub)[0]);
	pool<int> ids;
	for (Cell *barrier : barriers)
		ids.insert(barrier->attributes.at(id_attr).as_int());
	EXPECT_EQ(ids.size(), 3u);
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
	Pins expected = {t.child(u_c)->pins[0], t.child(u_inv2)->pins[0], t.child(u_sub)->findPin("a", 0)};
	EXPECT_EQ(sortedPins(ref.pins), sortedPins(expected));
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
	EXPECT_EQ(ref.pins[0]->dir(), RTLIL::PD_INPUT);
}

TEST_F(NetProtectTest, pinRefFindsTopPins)
{
	Wire *o = top->addWire("\\o");
	o->port_output = true;
	Wire *thru = top->addWire("\\thru");
	thru->port_output = true;
	top->fixup_ports();
	top->connect(o, State::S0);
	top->connect(thru, in);
	TrackedView t(d);
	TrackedRef port = pinRef({t.view->top()->findPin("in", 0)});
	Pins ref_pins = {t.view->top()->findPin("in", 0), t.view->top()->findPin("o", 0), t.child(u_inv0)->pins[0]};
	TrackedRef ref = pinRef(ref_pins);
	t.checkpoint({&port, &ref});
	top->rename(in, "\\in2");
	top->rename(out, "\\in");
	top->fixup_ports();
	t.next({&port, &ref});
	EXPECT_EQ(port.pins, Pins{t.view->top()->findPin("in2", 0)});
	Pins expected = {t.view->top()->findPin("in2", 0), t.view->top()->findPin("o", 0), t.child(u_inv0)->pins[0]};
	EXPECT_EQ(sortedPins(ref.pins), sortedPins(expected));
}

// protected flatten dissolves a scope with a public name, the ref follows its cell
// flatten keeps no name of a scope with a private name, so a protected one stays
TEST_F(NetProtectTest, flattenDissolvesOnlyAPublicScopeOfARef)
{
	ensurePasses();
	Cell *u_private = top->addCell("$u_private", "\\sub");
	u_private->setPort(ID(a), d0);
	TrackedView t(d);
	TrackedRef cell{.kind = TrackedRef::Kind::Instance, .instances = {t.view->instance(i1, t.child(u_sub))}};
	TrackedRef private_cell{.kind = TrackedRef::Kind::Instance};
	private_cell.instances = {t.view->instance(i1, t.child(u_private))};
	t.checkpoint({&cell, &private_cell});
	Pass::call(d, "flatten -noscopeinfo");
	ASSERT_EQ(top->cell("\\u_sub"), nullptr);
	ASSERT_EQ(top->cell("$u_private"), u_private);
	t.next({&cell, &private_cell});
	EXPECT_EQ(cell.instances, std::vector<const Netlist::Instance *>{t.child(top->cell("\\u_sub.i1"))});
	ASSERT_EQ(private_cell.instances.size(), 1u);
	EXPECT_EQ(private_cell.instances[0], t.view->instance(i1, t.child(u_private)));
	t.tracker.unprotect(d);
	EXPECT_FALSE(u_private->has_attribute(ID::keep_hierarchy));
}

// with no protect the private scope is gone, the one cell with the id is the cell of the ref
TEST_F(NetProtectTest, flattenOfAPrivateScopeKeepsTheRef)
{
	ensurePasses();
	top->rename(u_sub, "$u_sub");
	TrackedView t(d);
	TrackedRef cell{.kind = TrackedRef::Kind::Instance, .instances = {t.view->instance(i1, t.child(u_sub))}};
	t.tracker.checkpoint(*t.view, {&cell}, false);
	Pass::call(d, "flatten -noscopeinfo");
	ASSERT_EQ(top->cell("$u_sub"), nullptr);
	t.next({&cell});
	ASSERT_EQ(cell.instances.size(), 1u);
	EXPECT_TRUE(cell.instances[0]->cell->hasPort(ID::Y)); // only i1 has it
	EXPECT_FALSE(cell.gone);
}

// two private scopes of one module leave two cells with the id and no scope name, the ref takes none
TEST_F(NetProtectTest, twinsOfADissolvedPrivateScopeLoseTheRef)
{
	ensurePasses();
	top->rename(u_sub, "$u_sub");
	top->addCell("$u_twin", "\\sub")->setPort(ID(a), d0);
	TrackedView t(d);
	TrackedRef cell{.kind = TrackedRef::Kind::Instance, .instances = {t.view->instance(i1, t.child(u_sub))}};
	t.tracker.checkpoint(*t.view, {&cell}, false);
	Pass::call(d, "flatten -noscopeinfo");
	t.next({&cell});
	EXPECT_TRUE(cell.instances.empty());
	EXPECT_TRUE(cell.gone);
}

// the barrier of a hierarchical pin is in the parent, flatten leaves it and the pin is the leaf pins behind it
TEST_F(NetProtectTest, flattenMovesAHierPinToTheLeafPins)
{
	ensurePasses();
	TrackedView t(d);
	TrackedRef ref = pinRef({t.child(u_sub)->findPin("a", 0)});
	t.checkpoint({&ref});
	ASSERT_EQ(barriersOf(top).size(), 1u);
	EXPECT_TRUE(barriersOf(sub).empty());
	t.next({&ref});
	EXPECT_EQ(ref.pins, Pins{t.child(u_sub)->findPin("a", 0)});
	Pass::call(d, "flatten -noscopeinfo");
	t.next({&ref});
	Pins leaf_pins = {t.child(top->cell("\\u_sub.i1"))->pins[0], t.child(top->cell("\\u_sub.i2"))->pins[0]};
	EXPECT_EQ(sortedPins(ref.pins), sortedPins(leaf_pins));
}

// flatten joins a net on a port of its scope with the net above, the ref is the old pins of the net
TEST_F(NetProtectTest, mergedNetGivesItsOldPins)
{
	ensurePasses();
	TrackedView t(d);
	TrackedRef net{.kind = TrackedRef::Kind::Net, .nets = {t.child(u_sub)->findPin("a", 0)->inner}};
	t.tracker.checkpoint(*t.view, {&net}, false);
	Pass::call(d, "flatten -noscopeinfo");
	for (int run = 0; run < 2; run++) { // a rerun gives the same
		t.next({&net});
		EXPECT_TRUE(net.nets.empty());
		EXPECT_EQ(net.kind, TrackedRef::Kind::Pin);
		Pins leaf_pins = {t.child(top->cell("\\u_sub.i1"))->pins[0], t.child(top->cell("\\u_sub.i2"))->pins[0]};
		EXPECT_EQ(sortedPins(net.pins), sortedPins(leaf_pins));
	}
}

// a ref on a load below the hierarchical pin has its own barrier, the pin still is each load behind it
TEST_F(NetProtectTest, hierPinPassesTheBarrierOfALoadRef)
{
	ensurePasses();
	TrackedView t(d);
	TrackedRef ref = pinRef({t.child(u_sub)->findPin("a", 0)});
	TrackedRef load = pinRef({t.view->instance(i1, t.child(u_sub))->pins[0]});
	t.checkpoint({&ref, &load});
	Pass::call(d, "flatten -noscopeinfo");
	ASSERT_EQ(top->cell("\\u_sub"), nullptr);
	t.next({&ref, &load});
	Pins leaf_pins = {t.child(top->cell("\\u_sub.i1"))->pins[0], t.child(top->cell("\\u_sub.i2"))->pins[0]};
	EXPECT_EQ(sortedPins(ref.pins), sortedPins(leaf_pins));
	EXPECT_EQ(load.pins, Pins{leaf_pins[0]});
}

// splitnets drops the port wire anchors, the port name finds the pin
TEST_F(NetProtectTest, topPortFindsItsPinByName)
{
	TrackedView t(d);
	TrackedRef port = pinRef({t.view->top()->findPin("q", 1)});
	t.checkpoint({&port});
	q->attributes.clear();
	t.next({&port});
	EXPECT_EQ(port.pins, Pins{t.view->top()->findPin("q", 1)});
}

// one port wire lost its id, its name finds the pin next to the port that its id finds
TEST_F(NetProtectTest, topPortByNameNextToAPortById)
{
	TrackedView t(d);
	TrackedRef ports = pinRef({t.view->top()->findPin("in", 0), t.view->top()->findPin("q", 1)});
	t.checkpoint({&ports});
	q->attributes.clear();
	t.next({&ports});
	Pins expected = {t.view->top()->findPin("in", 0), t.view->top()->findPin("q", 1)};
	EXPECT_EQ(sortedPins(ports.pins), sortedPins(expected));
}

// a pass puts a load on the cut wire of a driver, the old pin is the loads behind its barrier
TEST_F(NetProtectTest, loadOnADriverCutWireGivesTheLoadsBehind)
{
	TrackedView t(d);
	TrackedRef ref = pinRef({t.child(u_inv0)->pins[1]});
	t.checkpoint({&ref});
	Cell *merged = top->addCell("\\merged", ID(INV));
	merged->setPort(ID(A), u_inv0->getPort(ID(Y)));
	t.next({&ref});
	EXPECT_TRUE(ref.gone);
	EXPECT_TRUE(ref.pins.empty());
	ASSERT_FALSE(ref.loads.empty());
	for (const Netlist::Pin *pin : ref.loads)
		EXPECT_NE(pin->inst->cell, merged);
}

// the ref goes on as its loads
TEST_F(NetProtectTest, checkpointOfAWireRefAnchorsItsLoads)
{
	TrackedView t(d);
	TrackedRef ref = pinRef({t.child(u_inv0)->pins[1]});
	t.checkpoint({&ref});
	top->addCell("\\merged", ID(INV))->setPort(ID(A), u_inv0->getPort(ID(Y)));
	t.next({&ref});
	size_t load_count = ref.loads.size();
	ASSERT_NE(load_count, 0u);
	t.checkpoint({&ref});
	t.next({&ref});
	EXPECT_FALSE(ref.gone);
	EXPECT_EQ(ref.pins.size(), load_count);
	EXPECT_TRUE(ref.loads.empty());
}

// flatten copies a barrier with its id
TEST_F(NetProtectTest, copyOfABarrierGetsItsOwnId)
{
	TrackedView t(d);
	TrackedRef first = pinRef({t.child(u_inv2)->pins[0]});
	t.checkpoint({&first});
	Wire *cut = top->addWire("$cut");
	cut->set_bool_attribute(d->twines().find("\\netview_cut"));
	Cell *copy = top->addCell("$copy", barriersOf(top)[0]);
	copy->setPort(ID::A, in);
	copy->setPort(ID::Y, cut);
	u_inv0->setPort(ID(A), cut);
	t.view = std::make_unique<NetView>(d);
	first = pinRef({t.child(u_inv2)->pins[0]});
	TrackedRef second = pinRef({t.child(u_inv0)->pins[0]});
	t.checkpoint({&first, &second});
	t.next({&first, &second});
	EXPECT_EQ(first.pins, Pins{t.child(u_inv2)->pins[0]});
	EXPECT_EQ(second.pins, Pins{t.child(u_inv0)->pins[0]});
}

// a pass put a second load on the cut wire
TEST_F(NetProtectTest, pinOnASharedCutWireGetsItsOwnBarrier)
{
	TrackedView t(d);
	TrackedRef ref = pinRef({t.child(u_inv2)->pins[0]});
	t.checkpoint({&ref});
	top->addCell("\\other", ID(INV))->setPort(ID(A), u_inv2->getPort(ID(A)));
	t.view = std::make_unique<NetView>(d);
	ref = pinRef({t.child(u_inv2)->pins[0]});
	t.checkpoint({&ref});
	t.next({&ref});
	EXPECT_EQ(ref.pins, Pins{t.child(u_inv2)->pins[0]});
}

TEST_F(NetProtectTest, plainBarrierOnACutWireIsPassed)
{
	TrackedView t(d);
	TrackedRef ref = pinRef({t.child(u_inv2)->pins[0]});
	t.checkpoint({&ref});
	Wire *behind = top->addWire("\\behind");
	top->addBarrier("\\user", u_inv2->getPort(ID(A)), behind);
	u_inv2->setPort(ID(A), behind);
	t.next({&ref});
	EXPECT_EQ(ref.pins, Pins{t.child(u_inv2)->pins[0]});
}

// opt_expr makes a gate a wire, the driver before it can have other loads
TEST_F(NetProtectTest, driverPinOfACellThatBecameAWireIsLost)
{
	Wire *between = top->addWire("\\between");
	Cell *before = top->addCell("\\before", ID(INV));
	before->setPort(ID(A), in);
	before->setPort(ID(Y), between);
	Cell *gate = top->addCell("\\gate", ID(INV));
	gate->setPort(ID(A), between);
	gate->setPort(ID(Y), top->addWire("\\after"));
	TrackedView t(d);
	TrackedRef ref = pinRef({t.child(gate)->pins[1]});
	t.checkpoint({&ref});
	top->connect(gate->getPort(ID(Y)), gate->getPort(ID(A)));
	top->remove(gate);
	t.next({&ref});
	EXPECT_TRUE(ref.gone);
	EXPECT_TRUE(ref.pins.empty());
	EXPECT_TRUE(ref.loads.empty());
}

// after clear, resolve finds nothing
TEST_F(NetProtectTest, clearForgetsTheAnchors)
{
	TrackedView t(d);
	TrackedRef cell{.kind = TrackedRef::Kind::Instance, .instances = {t.child(u_inv2)}};
	TrackedRef port = pinRef({t.view->top()->findPin("in", 0)});
	TrackedRef net{.kind = TrackedRef::Kind::Net, .nets = {t.view->top()->findPin("in", 0)->inner}};
	t.checkpoint({&cell, &port, &net});
	t.tracker.clear(d);
	t.next({&cell, &port, &net});
	EXPECT_TRUE(cell.instances.empty());
	EXPECT_TRUE(port.pins.empty()); // the name of a top port finds no pin
	EXPECT_TRUE(net.nets.empty());
	EXPECT_TRUE(cell.gone && port.gone && net.gone);
}

YOSYS_NAMESPACE_END
