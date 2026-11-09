#include "netviewHelpers.h"

#include "kernel/sigtools.h"

YOSYS_NAMESPACE_BEGIN

using NetProtectTest = NetViewTest;

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

TEST_F(NetProtectTest, clockPinKeepsABarrierInstance)
{
	TrackedView t(d);
	TrackedRef ref = pinRef({t.child(u_sub)->pins[0]});
	ref.hints.keep_as_instance = true;
	t.checkpoint({&ref});
	EXPECT_FALSE(t.view->upToDate());
	t.next({&ref});
	ASSERT_EQ(ref.result.barrier_a_pins.size(), 1u);
	ASSERT_EQ(ref.result.barrier_y_pins.size(), 1u);
	const Netlist::Pin *a = ref.result.barrier_a_pins[0];
	const Netlist::Pin *y = ref.result.barrier_y_pins[0];
	EXPECT_TRUE(a->inst->kind == Netlist::Instance::Kind::Barrier);
	EXPECT_EQ(a->dir(), Netlist::PortDir::Input);
	EXPECT_EQ(a->net, t.child(u_sub)->pins[0]->inner);
	EXPECT_EQ(y->net, t.view->instance(i1, t.child(u_sub))->pins[0]->net);
	EXPECT_NE(a->net, y->net);
	ASSERT_EQ(t.view->nets(a->inst).size(), 1u);
	EXPECT_EQ(a->inner, y->inner);
	Pins loads = {t.view->instance(i1, t.child(u_sub))->pins[0], t.view->instance(i2, t.child(u_sub))->pins[0]};
	EXPECT_EQ(sortedPins(ref.pins), sortedPins(loads));
	EXPECT_TRUE(ref.result.flattened_hier_pin);
	TrackedRef on_barrier = pinRef({a});
	t.with_barriers = false;
	t.checkpoint({&on_barrier});
	EXPECT_TRUE(on_barrier.origin.on_barrier_instance);
}

TEST_F(NetProtectTest, freedCutWireMakesTheViewStale)
{
	Wire *cut = top->addWire("$C");
	cut->set_bool_attribute(d->twines().add("\\netview_cut"));
	top->addBarrier("$Bx", cut, top->addWire("$c2"));
	u_inv2->setPort(ID(A), cut);
	TrackedView t(d);
	TrackedRef ref = pinRef({t.child(u_inv2)->pins[0]});
	t.checkpoint({&ref});
	EXPECT_FALSE(t.view->upToDate());
}

TEST_F(NetProtectTest, unprotectKeepsTheAnchors)
{
	ensurePasses();
	TrackedView t(d);
	TrackedRef cell{TrackedRef::Kind::Instance};
	cell.instances = {t.child(u_inv2)};
	t.checkpoint({&cell});
	EXPECT_TRUE(u_inv2->get_bool_attribute(ID::keep));
	EXPECT_EQ(barriersOf(top).size(), 2u); // a barrier at each pin
	t.tracker.unprotect(d);
	EXPECT_FALSE(u_inv2->has_attribute(ID::keep));
	EXPECT_EQ(top->cells().size(), 3u);
	EXPECT_FALSE(t.view->upToDate());
	t.next({&cell});
	EXPECT_EQ(cell.instances, std::vector<const Netlist::Instance *>{t.child(u_inv2)});
}

TEST_F(NetProtectTest, removedCellKeepsItsLoads)
{
	TrackedView t(d);
	TrackedRef cell{TrackedRef::Kind::Instance};
	cell.instances = {t.child(u_inv2)};
	t.checkpoint({&cell});
	// a pass makes the cell a wire
	top->connect(u_inv2->getPort(ID(Y)), u_inv2->getPort(ID(A)));
	top->remove(u_inv2);
	t.next({&cell});
	EXPECT_TRUE(cell.instances.empty());
	EXPECT_EQ(cell.result.loads_beyond, Pins{t.view->top()->findPin("out", 0)});
	EXPECT_TRUE(cell.removedButLoadsKept());
}

// The name finds no port, the barrier finds it by its signal
TEST_F(NetProtectTest, netBarrierFindsTheNetOfItsScope)
{
	TrackedView t(d);
	TrackedRef net{TrackedRef::Kind::Net};
	net.nets = {t.child(u_inv2)->pins[0]->net};
	t.checkpoint({&net});
	// splitnets drops the anchors of the wire
	p->attributes.clear();
	t.next({&net});
	EXPECT_EQ(net.nets, std::vector<const Netlist::Net *>{t.child(u_inv2)->pins[0]->net});
}

TEST_F(NetProtectTest, loopOfNewBuffersEnds)
{
	TrackedView t(d);
	TrackedRef ref = pinRef({t.child(u_inv2)->pins[0]});
	t.checkpoint({&ref});
	// a pass puts a loop of buffers on the cut wire
	SigBit cut = u_inv2->getPort(ID(A));
	Wire *b = top->addWire("\\b");
	Cell *b1 = top->addCell("$b1", ID($_BUF_));
	b1->setPort(ID::A, cut);
	b1->setPort(ID::Y, b);
	Cell *b2 = top->addCell("$b2", ID($_BUF_));
	b2->setPort(ID::A, b);
	b2->setPort(ID::Y, cut);
	t.next({&ref});
	EXPECT_EQ(ref.pins, Pins{t.child(u_inv2)->pins[0]});
}

TEST_F(NetProtectTest, ringOfNewBuffersOnAPartEnds)
{
	Wire *n = top->addWire("\\n");
	top->connect(n, d0);
	TrackedView t(d);
	TrackedRef net{TrackedRef::Kind::Net};
	net.nets = {t.child(u_inv0)->pins[1]->net};
	t.checkpoint({&net});
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
	t.next({&net});
	EXPECT_FALSE(net.nets.empty());
}

// insbuf puts a buffer between a top input and its barrier, a pass renames the port
TEST_F(NetProtectTest, portBarrierPassesANewBuffer)
{
	TrackedView t(d);
	TrackedRef port = pinRef({t.view->top()->findPin("q", 1)}, TrackedRef::Kind::TopPort);
	t.checkpoint({&port});
	Wire *w = top->addWire("\\w");
	Cell *buf = top->addCell("$buf", ID($_BUF_));
	buf->setPort(ID::A, SigBit(q, 1));
	buf->setPort(ID::Y, w);
	ASSERT_EQ(barriersOf(top).size(), 1u);
	barriersOf(top)[0]->setPort(ID::A, w);
	q->attributes.clear();
	top->rename(q, "\\q_renamed");
	top->fixup_ports();
	t.next({&port});
	EXPECT_EQ(port.pins, Pins{t.view->top()->findPin("q_renamed", 1)});
}

TEST_F(NetProtectTest, newBarriersSkipIdsInUse)
{
	IdString id_attr;
	{
		TrackedView first(d);
		TrackedRef in_sub = pinRef({first.view->instance(i1, first.child(u_sub))->pins[0]});
		first.checkpoint({&in_sub});
		id_attr = d->twines().find("\\netview_anchor");
		Cell *read_back = barriersOf(sub)[0];
		read_back->attributes[id_attr] = Const(read_back->attributes.at(id_attr).as_int() + 1);
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

TEST_F(NetProtectTest, inoutPinIsALoadBeyondABarrier)
{
	Cell *b = addBidiCell(d, top, d0);
	TrackedView t(d);
	TrackedRef ref{TrackedRef::Kind::Instance};
	ref.instances = {t.child(u_inv0)};
	t.checkpoint({&ref});
	t.next({&ref});
	const Pins &loads = ref.result.loads_beyond;
	EXPECT_NE(std::find(loads.begin(), loads.end(), t.child(b)->pins[0]), loads.end());
	EXPECT_NE(std::find(loads.begin(), loads.end(), t.view->instance(i1, t.child(u_sub))->pins[0]), loads.end());
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

TEST_F(NetProtectTest, flattenCopyOfAKeptCellKeepsItsPath)
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
	TrackedView t(d, /*with_barriers=*/false);
	TrackedRef ref = pinRef({t.view->instance(i1, t.view->instance(mid->cell("\\s"), t.child(m1)))->pins[0]});
	t.checkpoint({&ref});
	Pass::call(d, "flatten");
	t.next({&ref});
	ASSERT_EQ(ref.pins.size(), 1u);
	EXPECT_EQ(ref.pins[0]->inst->parent, t.child(top->cell("\\m1.s")));
}

// splitnets drops the anchors of the port wire, the port name finds the pin
TEST_F(NetProtectTest, topPortFindsItsPinByName)
{
	TrackedView t(d, /*with_barriers=*/false);
	TrackedRef port = pinRef({t.view->top()->findPin("q", 1)}, TrackedRef::Kind::TopPort);
	t.checkpoint({&port});
	q->attributes.clear();
	t.next({&port});
	EXPECT_EQ(port.pins, Pins{t.view->top()->findPin("q", 1)});
}

// after clear, resolve finds nothing
TEST_F(NetProtectTest, clearForgetsTheAnchors)
{
	TrackedView t(d, /*with_barriers=*/false);
	TrackedRef cell{TrackedRef::Kind::Instance};
	cell.instances = {t.child(u_inv2)};
	t.checkpoint({&cell});
	t.tracker.clear(d);
	t.next({&cell});
	EXPECT_TRUE(cell.instances.empty());
}

YOSYS_NAMESPACE_END
