#include "netviewHelpers.h"

YOSYS_NAMESPACE_BEGIN

TEST_F(NetViewTest, buildsInstancesPinsNetsTerms)
{
	NetView view;
	view.build(d);
	Netlist::Instance *t = view.top();
	ASSERT_NE(t, nullptr);
	EXPECT_TRUE(t->isTop());
	EXPECT_EQ(t->id, 0u);
	EXPECT_EQ(t->name, "top");
	EXPECT_FALSE(t->isLeaf());
	EXPECT_EQ(view.module(t), top);
	EXPECT_EQ(t->children.size(), 3u);

	Netlist::Instance *isub = topChild(view, u_sub);
	Netlist::Instance *iinv0 = topChild(view, u_inv0);
	ASSERT_NE(isub, nullptr);
	EXPECT_FALSE(isub->isLeaf());
	EXPECT_TRUE(iinv0->isLeaf());
	EXPECT_NE(iinv0->kind, Netlist::Instance::Kind::InternalCell);
	EXPECT_EQ(isub->parent, t);
	EXPECT_EQ(view.module(isub), sub);
	EXPECT_EQ(view.scope(sub), isub);
	EXPECT_EQ(view.cell(iinv0), u_inv0);
	EXPECT_EQ(iinv0->type, "INV");
	EXPECT_EQ(isub->children.size(), 2u);

	// top ports: in, out, q[3:0], s
	EXPECT_EQ(t->pins.size(), 7u);
	for (Netlist::Pin *pin : t->pins) {
		EXPECT_EQ(pin->net, nullptr);
		ASSERT_NE(pin->term, nullptr);
		EXPECT_EQ(pin->term->net->scope, t);
	}
	// ports shared per library type
	ASSERT_EQ(iinv0->pins.size(), 2u);
	EXPECT_EQ(iinv0->pins[0]->port().name, "A");
	EXPECT_EQ(iinv0->pins[1]->port().name, "Y");
	EXPECT_EQ(iinv0->ports, topChild(view, u_inv2)->ports);
	ASSERT_EQ(isub->pins.size(), 5u);
	Netlist::Pin *y0 = isub->pins[1];
	EXPECT_EQ(y0->port().name, "y");
	EXPECT_EQ(y0->bit, 0);
	EXPECT_EQ(isub->findPin("y", 0), y0);
	EXPECT_EQ(isub->findPin("y", 4), nullptr);
	ASSERT_NE(y0->term, nullptr);
	EXPECT_EQ(y0->term->net->scope, isub);
	EXPECT_EQ(y0->term->net, view.instance(i1)->pins[1]->net);
	EXPECT_EQ(isub->pins[2]->net, nullptr); // y[1] unconnected
	ASSERT_NE(isub->pins[2]->term, nullptr);
}

TEST_F(NetViewTest, hdlIndexDirAndScalar)
{
	NetView view;
	view.build(d);
	std::vector<Netlist::Pin *> qpins;
	Netlist::Pin *spin = nullptr;
	for (Netlist::Pin *pin : view.top()->pins) {
		if (pin->port().name == "q")
			qpins.push_back(pin);
		if (pin->port().name == "s")
			spin = pin;
	}
	ASSERT_EQ(qpins.size(), 4u);
	EXPECT_EQ(qpins[0]->hdlIndex(), 0);
	EXPECT_EQ(qpins[3]->hdlIndex(), 3);
	EXPECT_FALSE(qpins[0]->port().scalar());
	ASSERT_NE(spin, nullptr);
	EXPECT_EQ(spin->hdlIndex(), 5);
	Netlist::Instance *isub = topChild(view, u_sub);
	EXPECT_EQ(isub->pins[1]->hdlIndex(), 3); // y[0:3]: bit 0 is y[3]
	EXPECT_EQ(isub->pins[4]->hdlIndex(), 0);
	EXPECT_EQ(topChild(view, u_inv0)->pins[0]->dir(), Netlist::PortDir::Input);
	EXPECT_EQ(topChild(view, u_inv0)->pins[1]->dir(), Netlist::PortDir::Output);
	EXPECT_EQ(isub->pins[1]->dir(), Netlist::PortDir::Output);
}

TEST_F(NetViewTest, namesAliasesAndConstants)
{
	Cell *u_x = top->addCell("\\u_x", ID(INV));
	u_x->setPort(ID(A), State::Sx);
	NetView view;
	view.build(d);
	Netlist::Instance *t = view.top();
	std::vector<Netlist::Net *> zeros = view.constNets(Netlist::Net::Const::Zero);
	ASSERT_EQ(zeros.size(), 1u);
	Netlist::Net *zero = zeros[0];
	EXPECT_EQ(zero->scope, t);
	EXPECT_EQ(zero->constant, Netlist::Net::Const::Zero);
	EXPECT_TRUE(view.constNets(Netlist::Net::Const::One).empty());
	bool found = false;
	for (const Netlist::NetAlias &alias : view.aliases(t)) {
		if (alias.name.wire == "tie")
			found = alias.net == zero;
	}
	EXPECT_TRUE(found);
	EXPECT_EQ(topChild(view, u_x)->pins[0]->net, nullptr);
	Netlist::Net *d0_net = topChild(view, u_inv0)->pins[1]->net;
	EXPECT_EQ(d0_net, topChild(view, u_sub)->pins[0]->net);
	EXPECT_EQ(d0_net->pins.size(), 2u);
	EXPECT_EQ(view.name(d0_net), (Netlist::NetName{"d0", 0, true}));
	EXPECT_FALSE(view.nets(t).empty());
	EXPECT_EQ(view.nets(topChild(view, u_inv0)).size(), 0u); // leaves own none
}

TEST_F(NetViewTest, driversAreTopInputsAndLeafOutputs)
{
	NetView view;
	view.build(d);
	for (Netlist::Pin *pin : view.top()->pins)
		EXPECT_EQ(pin->isDriver(), pin->port().name != "out") << pin->port().name;
	Netlist::Instance *iinv0 = topChild(view, u_inv0);
	EXPECT_FALSE(iinv0->pins[0]->isDriver());
	EXPECT_TRUE(iinv0->pins[1]->isDriver());
	for (Netlist::Pin *pin : topChild(view, u_sub)->pins)
		EXPECT_FALSE(pin->isDriver());
}

TEST_F(NetViewTest, instancesFollowCreationOrderDepthFirst)
{
	NetView view;
	view.build(d);
	Netlist::Instance *isub = topChild(view, u_sub);
	std::vector<Netlist::Instance *> order = {topChild(view, u_inv0), isub, view.instance(i1), view.instance(i2),
						  topChild(view, u_inv2)};
	for (size_t i = 0; i < order.size(); i++)
		EXPECT_EQ(order[i]->id, i + 1) << order[i]->name;
	std::vector<Netlist::Instance *> children = {topChild(view, u_inv0), topChild(view, u_sub), topChild(view, u_inv2)};
	EXPECT_EQ(view.top()->children, children);

	// write_verilog sorts in place
	top->sort();
	view.clear();
	view.build(d);
	children = {topChild(view, u_inv0), topChild(view, u_inv2), topChild(view, u_sub)};
	EXPECT_EQ(view.top()->children, children);
}

TEST_F(NetViewTest, clearRestartsIds)
{
	NetView view;
	view.build(d);
	const Netlist::Pin *pin = view.top()->pins[0];
	pin->user = 7; // a consumer writes it through a const pin
	view.clear();
	EXPECT_FALSE(view.built());
	EXPECT_FALSE(view.upToDate());
	EXPECT_TRUE(d->monitors.empty());
	view.build(d);
	EXPECT_TRUE(view.upToDate());
	EXPECT_EQ(view.top()->pins[0]->id, 1u);
	EXPECT_EQ(view.top()->pins[0]->user, 0u);
	EXPECT_EQ(view.top()->children[0]->id, 1u);
	EXPECT_EQ(view.nets(view.top())[0]->id, 1u);
}

TEST_F(NetViewTest, namingPrefersKeepThenShallowHdlpath)
{
	Wire *d1 = top->addWire("\\d1");
	top->connect(d1, d0);
	NetView view;
	view.build(d);
	ASSERT_EQ(view.name(topChild(view, u_inv0)->pins[1]->net).wire, "d0");

	d1->set_bool_attribute(ID::keep);
	view.clear();
	view.build(d);
	EXPECT_EQ(view.name(topChild(view, u_inv0)->pins[1]->net).wire, "d1");

	d1->attributes.erase(ID::keep);
	d0->set_hdlname_attribute({"u", "d0"});
	view.clear();
	view.build(d);
	EXPECT_EQ(view.name(topChild(view, u_inv0)->pins[1]->net).wire, "d1");
}

// i -> u1 -> $n (pa, pb) -> u2 -> o
static Design *aliasDesign(const std::vector<std::string> &order)
{
	Design *design = new Design;
	addInv(design, "\\INV");
	Module *m = design->addModule(ID(top));
	m->set_bool_attribute(ID::top);
	for (const std::string &name : order)
		m->addWire(name);
	m->wire(ID(i))->port_input = true;
	m->wire(ID(o))->port_output = true;
	m->fixup_ports();
	Cell *u1 = m->addCell("\\u1", ID(INV));
	u1->setPort(ID::A, m->wire(ID(i)));
	u1->setPort(ID::Y, m->wire("$n"));
	Cell *u2 = m->addCell("\\u2", ID(INV));
	u2->setPort(ID::A, m->wire("$n"));
	u2->setPort(ID::Y, m->wire(ID(o)));
	m->connect(m->wire("\\pb"), m->wire("$n"));
	m->connect(m->wire("\\pa"), m->wire("$n"));
	return design;
}

TEST(NetViewNamingTest, namingIsIndependentOfWireOrder)
{
	std::vector<std::vector<std::string>> orders = {
	  {"\\i", "\\o", "\\zz", "\\pa", "$n", "\\pb"},
	  {"\\pb", "$n", "\\o", "\\pa", "\\i", "\\zz"},
	};
	for (const std::vector<std::string> &order : orders) {
		Design *design = aliasDesign(order);
		NetView view;
		view.build(design);
		Cell *u1 = design->module(ID(top))->cell("\\u1");
		EXPECT_EQ(view.name(topChild(view, u1)->pins[1]->net), (Netlist::NetName{"pa", 0, true}));
		EXPECT_EQ(view.aliases(view.top()).size(), 4u); // zz has no net
		view.clear();
		delete design;
	}
}

TEST_F(NetViewTest, buildableReasons)
{
	std::string reason;
	EXPECT_TRUE(NetView::buildable(d, reason));

	sub->addProcess("\\proc");
	EXPECT_FALSE(NetView::buildable(d, reason));
	EXPECT_NE(reason.find("(run proc)"), std::string::npos) << reason;
	sub->remove(sub->processes.at(d->twines().find("\\proc")));

	Cell *u_sub2 = top->addCell("\\u_sub2", "\\sub");
	EXPECT_FALSE(NetView::buildable(d, reason));
	EXPECT_NE(reason.find("(run uniquify)"), std::string::npos) << reason;
	top->remove(u_sub2);
	Cell *self = sub->addCell("\\self", "\\sub");
	EXPECT_FALSE(NetView::buildable(d, reason));
	EXPECT_NE(reason.find("contains itself"), std::string::npos) << reason;
	sub->remove(self);

	Design empty;
	EXPECT_FALSE(NetView::buildable(&empty, reason));
	EXPECT_NE(reason.find("no top"), std::string::npos);
}

TEST_F(NetViewTest, selectionDoesNotMatter)
{
	NetView view;
	view.build(d);
	d->selection().select(sub);
	view.recheck();
	EXPECT_TRUE(view.upToDate());
}

// Stale after an edit, then rebuilt for the next
static void expectStale(NetView &view, Design *d)
{
	view.recheck();
	EXPECT_FALSE(view.upToDate());
	view.clear();
	view.build(d);
	EXPECT_TRUE(view.upToDate());
}

TEST_F(NetViewTest, fingerprintSeesEdits)
{
	NetView view;
	view.build(d);

	top->attributes.erase(ID::top);
	sub->set_bool_attribute(ID::top);
	expectStale(view, d);
	sub->attributes.erase(ID::top);
	top->set_bool_attribute(ID::top);
	expectStale(view, d);

	inv2->hashidx_++; // a clone: same pointer, new hashidx_
	expectStale(view, d);
	inv->wire(ID(A))->port_output = true; // blackbox port
	expectStale(view, d);
	u_inv2->set_hdlname_attribute({"blk", "u_inv2"});
	expectStale(view, d);
	d0->set_bool_attribute(ID::keep);
	expectStale(view, d);

	Wire *b_out = top->addWire("\\b_out");
	expectStale(view, d);
	Cell *barrier = top->addBarrier("$b", in, b_out);
	expectStale(view, d);
	top->remove(barrier);
	expectStale(view, d);
}

TEST_F(NetViewTest, staleViewKeepsNames)
{
	NetView view;
	view.build(d);
	Netlist::Net *d0_net = topChild(view, u_inv0)->pins[1]->net;
	top->rename(d0, "\\renamed");
	top->remove(pool<Wire *>{d0});
	view.recheck();
	EXPECT_FALSE(view.upToDate());
	EXPECT_EQ(view.name(d0_net), (Netlist::NetName{"d0", 0, true}));
}

TEST_F(NetViewTest, monitorEventsMakeTheViewStale)
{
	NetView view;
	view.build(d);
	u_inv2->setPort(ID(A), in);
	EXPECT_FALSE(view.upToDate());

	NetView other;
	other.build(d);
	top->connect(p, d0);
	EXPECT_FALSE(other.upToDate());

	NetView third;
	third.build(d);
	d->addModule("\\extra");
	EXPECT_FALSE(third.upToDate());
}

TEST_F(NetViewTest, deletedDesignMakesTheViewStale)
{
	Design *other = new Design;
	Module *m = other->addModule(ID(top));
	m->addWire(ID(a))->port_input = true;
	m->fixup_ports();
	NetView view;
	view.build(other);
	delete other;
	view.recheck();
	EXPECT_FALSE(view.upToDate());
}

static Module *addWrapper(Design *design, const std::string &name, const std::string &child, const std::string &type, bool mid_inv)
{
	Module *module = design->addModule(name);
	Wire *a = module->addWire(ID(a));
	a->port_input = true;
	Wire *y = module->addWire(ID(y));
	y->port_output = true;
	module->fixup_ports();
	Wire *in = a;
	if (mid_inv) {
		in = module->addWire("\\mid");
		Cell *i0 = module->addCell("\\i0", ID(INV));
		i0->setPort(ID(A), a);
		i0->setPort(ID(Y), in);
	}
	Cell *cell = module->addCell(child, type);
	cell->setPort(type == "\\INV" ? ID(A) : ID(a), in);
	cell->setPort(type == "\\INV" ? ID(Y) : ID(y), y);
	return module;
}

// top: a -> u1 (sub: a -> i0 -> mid -> u2 (inner: j)) -> y
static Design *flatDesign()
{
	ensurePasses();
	Design *design = new Design;
	addInv(design, "\\INV");
	addWrapper(design, "\\inner", "\\j", "\\INV", false);
	addWrapper(design, "\\sub", "\\u2", "\\inner", true);
	addWrapper(design, "\\top", "\\u1", "\\sub", false)->set_bool_attribute(ID::top);
	Pass::call(design, "flatten");
	return design;
}

TEST(NetViewFlatTest, scopeinfoIsTransparent)
{
	Design *design = flatDesign();
	Module *top = design->module(ID(top));
	ASSERT_NE(top->cell("\\u1"), nullptr);
	EXPECT_EQ(top->cell("\\u1")->type, ID($scopeinfo));
	NetView view;
	view.build(design);
	EXPECT_EQ(topChild(view, top->cell("\\u1")), nullptr);
	EXPECT_EQ(view.top()->children.size(), 2u); // u1.i0, u1.u2.j
	delete design;
}

TEST(NetViewFlatTest, hdlnameBecomesHdlpath)
{
	Design *design = flatDesign();
	Module *top = design->module(ID(top));
	NetView view;
	view.build(design);
	Netlist::Instance *i0 = topChild(view, top->cell("\\u1.i0"));
	Netlist::Instance *j = topChild(view, top->cell("\\u1.u2.j"));
	ASSERT_NE(i0, nullptr);
	ASSERT_NE(j, nullptr);
	EXPECT_EQ(i0->name, "u1.i0");
	EXPECT_EQ(i0->hdlpath, (std::vector<std::string>{"u1", "i0"}));
	EXPECT_EQ(j->hdlpath, (std::vector<std::string>{"u1", "u2", "j"}));
	Netlist::Net *mid = i0->pins[1]->net;
	bool found = false;
	for (const Netlist::NetAlias &alias : view.aliases(view.top())) {
		if (alias.name.wire == "u1.mid")
			found = alias.net == mid && alias.name.hdlpath == std::vector<std::string>{"u1", "mid"};
	}
	EXPECT_TRUE(found);

	Netlist::Net *y = j->pins[1]->net;
	EXPECT_EQ(view.name(y), (Netlist::NetName{"y", 0, true}));
	Netlist::Net *a = i0->pins[0]->net;
	EXPECT_EQ(view.name(a), (Netlist::NetName{"a", 0, true}));
	EXPECT_EQ(view.name(mid), (Netlist::NetName{"u1.mid", 0, true, {"u1", "mid"}})); // also u1.u2.a
	delete design;
}

TEST_F(NetViewTest, buildableRefusesRangeOverflow)
{
	std::string reason;
	top->addWire("\\huge", 2)->start_offset = INT_MAX - 1; // fits: [INT_MAX:INT_MAX-1]
	ASSERT_TRUE(NetView::buildable(d, reason)) << reason;
	top->wire("\\huge")->start_offset = INT_MAX;
	EXPECT_FALSE(NetView::buildable(d, reason));
	EXPECT_NE(reason.find("huge"), std::string::npos) << reason;
	top->remove(pool<Wire *>{top->wire("\\huge")});
	ASSERT_TRUE(NetView::buildable(d, reason)) << reason;
	inv->addWire(ID(B), 2)->start_offset = INT_MAX; // [INT_MAX+1:INT_MAX]
	inv->wire(ID(B))->port_input = true;
	inv->fixup_ports();
	EXPECT_FALSE(NetView::buildable(d, reason));
	EXPECT_NE(reason.find("INV"), std::string::npos) << reason;
}

static std::vector<std::string> hdlpathOfName(const std::string &name)
{
	Design design;
	addInv(&design, "\\INV");
	Module *m = design.addModule(ID(top));
	m->set_bool_attribute(ID::top);
	Cell *cell = m->addCell(name, ID(INV));
	NetView view;
	view.build(&design);
	return topChild(view, cell)->hdlpath;
}

TEST(NetViewNameTest, flattenNamesGiveSourcePath)
{
	EXPECT_EQ(hdlpathOfName("$flatten\\u1.\\l0.$and$x.v:3$7"), (std::vector<std::string>{"u1", "l0", "$and$x.v:3$7"}));
	EXPECT_EQ(hdlpathOfName("$flatten\\u1/$y"), (std::vector<std::string>{"u1", "$y"}));
	EXPECT_EQ(hdlpathOfName("$flatten\\u1_\\l0_$y"), (std::vector<std::string>{"u1", "l0", "$y"}));
	EXPECT_TRUE(hdlpathOfName("$and$x.v:3$7").empty());
	EXPECT_TRUE(hdlpathOfName("$flatten\\u1").empty());
}

TEST(NetViewNameTest, publicNamesAreUnescaped)
{
	Design design;
	Module *bb = design.addModule("\\BB");
	bb->addWire("\\$a")->port_input = true;
	bb->addWire("$p")->port_input = true; // private
	bb->addWire(ID(Y))->port_output = true;
	bb->fixup_ports();
	bb->set_bool_attribute(ID::blackbox);
	Module *m = design.addModule(ID(top));
	m->set_bool_attribute(ID::top);
	Wire *i = m->addWire("\\1in");
	i->port_input = true;
	Wire *o = m->addWire(ID(o));
	o->port_output = true;
	m->fixup_ports();
	Cell *u = m->addCell("\\$u", "\\BB");
	u->setPort("\\$a", i);
	u->setPort("$p", i);
	u->setPort(ID(Y), o);
	NetView view;
	view.build(&design);
	Netlist::Instance *iu = topChild(view, u);
	EXPECT_EQ(iu->name, "$u");
	ASSERT_EQ(view.top()->ports->size(), 2u);
	EXPECT_TRUE((*view.top()->ports)[0].name == "1in" || (*view.top()->ports)[1].name == "1in");
	ASSERT_EQ(iu->pins.size(), 3u);
	for (Netlist::Pin *pin : iu->pins) {
		const std::string &port = pin->port().name;
		EXPECT_TRUE(port == "$a" || port == "$p" || port == "Y") << port;
		ASSERT_NE(pin->net, nullptr) << port;
		EXPECT_EQ(view.name(pin->net).wire, port == "Y" ? "o" : "1in") << port;
	}
}

TEST_F(NetViewTest, oneBitBusesKeepTheirIndex)
{
	Wire *z = top->addWire(ID(z));
	z->port_input = true;
	z->set_bool_attribute(ID::single_bit_vector);
	top->fixup_ports();
	NetView view;
	view.build(d);
	int buses = 0;
	for (Netlist::Pin *pin : view.top()->pins) {
		const std::string &port = pin->port().name;
		if (port != "s" && port != "z")
			continue;
		buses++;
		bool bus = port == "z";
		EXPECT_EQ(pin->port().scalar(), !bus) << port;
		EXPECT_EQ(view.name(pin->term->net).scalar, !bus) << port;
		EXPECT_EQ(view.name(pin->term->net).index, port == "s" ? 5 : 0);
	}
	EXPECT_EQ(buses, 2);
	EXPECT_TRUE(topChild(view, u_inv0)->pins[0]->port().scalar());
	EXPECT_TRUE(view.name(topChild(view, u_inv0)->pins[1]->net).scalar);
}

TEST_F(NetViewTest, zeroWidthPortsHaveNoPort)
{
	Wire *z = top->addWire(ID(z), 0);
	z->port_input = true;
	top->fixup_ports();
	Module *zb = d->addModule("\\ZB");
	zb->addWire(ID(A), 0)->port_input = true;
	zb->addWire(ID(Y))->port_output = true;
	zb->fixup_ports();
	zb->set_bool_attribute(ID::blackbox);
	Cell *u_z = top->addCell("\\u_z", "\\ZB");
	u_z->setPort(ID(Y), p);
	NetView view;
	view.build(d);
	for (const Netlist::Port &shape : *view.top()->ports)
		EXPECT_NE(shape.width, 0) << shape.name;
	EXPECT_EQ(view.top()->ports->size(), 4u); // in, out, q, s
	ASSERT_EQ(topChild(view, u_z)->ports->size(), 1u);
	EXPECT_EQ((*topChild(view, u_z)->ports)[0].name, "Y");
}

TEST_F(NetViewTest, unknownCellTypeIsACommandError)
{
	top->addCell("\\u_unknown", "\\UNKNOWN");
	auto scope = logger().error_throw_scope();
	NetView view;
	EXPECT_THROW(view.build(d), log_cmd_error_exception);
	EXPECT_FALSE(view.built());
	EXPECT_TRUE(d->monitors.empty());
	top->remove(top->cell("\\u_unknown"));
	view.build(d);
	EXPECT_TRUE(view.upToDate());
}

struct NoCellLibrary : Netlist::CellLibrary {
	bool ports(const Netlist::Instance &, std::vector<Netlist::Port> &) override { return false; }
};

TEST_F(NetViewTest, typeNotInLibraryTakesTheYosysPorts)
{
	NoCellLibrary library;
	NetView view;
	int warnings = logger().get_warnings_total();
	view.build(d, {&library});
	EXPECT_EQ(logger().get_warnings_total(), warnings + 1);
	const std::vector<Netlist::Port> &ports = *topChild(view, u_inv0)->ports;
	ASSERT_EQ(ports.size(), 2u);
	EXPECT_EQ(ports[0].name, "A");
	EXPECT_EQ(ports[1].name, "Y");
}

TEST_F(NetViewTest, directEditsNeedRecheck)
{
	Cell *u_spare = top->addCell("\\u_spare", ID(INV)); // no connections
	NetView view;
	view.build(d);
	u_inv2->type = d->twines().add("\\INV2");
	EXPECT_TRUE(view.upToDate());
	view.recheck();
	EXPECT_FALSE(view.upToDate());
	u_inv2->type = ID(INV);
	view.recheck();
	EXPECT_FALSE(view.upToDate());

	view.clear();
	view.build(d);
	top->remove(u_spare);
	EXPECT_TRUE(view.upToDate());
	view.recheck();
	EXPECT_FALSE(view.upToDate());

	view.clear();
	view.build(d);
	top->rename(d0, "\\renamed");
	EXPECT_TRUE(view.upToDate());
	view.recheck();
	EXPECT_FALSE(view.upToDate());
}

// $pre -> $barrier -> d0
TEST_F(NetViewTest, barriersAreTransparent)
{
	Wire *pre = top->addWire("$pre");
	u_inv0->setPort(ID(Y), pre);
	Cell *barrier = top->addBarrier("$b", pre, d0);
	NetView view;
	view.build(d);
	EXPECT_EQ(topChild(view, barrier), nullptr);
	EXPECT_EQ(view.top()->children.size(), 3u);
	Netlist::Net *driven = topChild(view, u_inv0)->pins[1]->net;
	EXPECT_EQ(driven, topChild(view, u_sub)->pins[0]->net);
	EXPECT_EQ(view.name(driven), (Netlist::NetName{"d0", 0, true}));
	EXPECT_EQ(driven->pins.size(), 2u);
}

TEST_F(NetViewTest, connectAndInputPortAreTransparent)
{
	Wire *pre = top->addWire("$pre");
	u_inv0->setPort(ID(Y), pre);
	Cell *connect = top->addCell("$c", ID($connect));
	connect->setParam(ID::WIDTH, 1);
	connect->setPort(ID::A, pre);
	connect->setPort(ID::B, d0);
	Cell *input = top->addCell("$i", ID($input_port));
	input->setParam(ID::WIDTH, 1);
	input->setPort(ID::Y, in);
	NetView view;
	view.build(d);
	EXPECT_EQ(topChild(view, connect), nullptr);
	EXPECT_EQ(topChild(view, input), nullptr);
	EXPECT_EQ(view.top()->children.size(), 3u);
	Netlist::Net *driven = topChild(view, u_inv0)->pins[1]->net;
	EXPECT_EQ(driven, topChild(view, u_sub)->pins[0]->net);
}

TEST_F(NetViewTest, barrierOnAConstantKeepsItsNet)
{
	Wire *c = top->addWire(ID(c));
	top->connect(c, State::S1);
	Cell *barrier = top->addBarrier("$b", c, p);
	NetView view;
	view.build(d);
	EXPECT_EQ(topChild(view, barrier), nullptr);
	Netlist::Net *net = topChild(view, u_inv2)->pins[0]->net;
	ASSERT_NE(net, nullptr);
	EXPECT_EQ(net->constant, Netlist::Net::Const::None);
	EXPECT_EQ(view.name(net).wire, "p");
	EXPECT_EQ(net->pins.size(), 2u);
}

TEST_F(NetViewTest, barrierOntoAConstantKeepsTheDrivenNet)
{
	Wire *k = top->addWire("\\k");
	top->connect(k, State::S0);
	top->addBarrier("$b", d0, k);
	NetView view;
	view.build(d);
	Netlist::Net *net = topChild(view, u_inv0)->pins[1]->net;
	EXPECT_EQ(net->constant, Netlist::Net::Const::None);
	EXPECT_EQ(view.name(net).wire, "d0");
}

// instances but the top, nets and pins below a scope
static void walk(const NetView &view, const Netlist::Instance *scope, NetView::Counts &counts)
{
	counts.nets += view.nets(scope).size();
	for (const Netlist::Instance *child : scope->children) {
		counts.instances++;
		counts.pins += child->pins.size();
		if (!child->isLeaf())
			walk(view, child, counts);
	}
}

TEST_F(NetViewTest, countsMatchAWalk)
{
	NetView view;
	view.build(d);
	NetView::Counts walked = {0, 0, view.top()->pins.size()};
	walk(view, view.top(), walked);
	EXPECT_EQ(view.counts(), walked);
	EXPECT_EQ(walked.instances, 5u); // u_inv0, u_sub, u_inv2, i1 and i2
}

TEST_F(NetViewTest, countsOfAnUnbuiltViewAreZero)
{
	NetView view;
	EXPECT_EQ(view.counts(), NetView::Counts{});
	view.build(d);
	EXPECT_NE(view.counts(), NetView::Counts{});
	view.clear();
	EXPECT_EQ(view.counts(), NetView::Counts{});
}

TEST_F(NetViewTest, splitBitsOfAFlatVectorKeepTheirIndex)
{
	Wire *w0 = top->addWire("\\u.w[0]");
	Wire *w1 = top->addWire("\\u.w[1]");
	w1->start_offset = 1;
	w0->set_hdlname_attribute({"u", "w"});
	w1->set_hdlname_attribute({"u", "w"});
	Cell *c = top->addCell("\\c", ID(INV));
	c->setPort(ID(A), w1);
	NetView view;
	view.build(d);
	EXPECT_EQ(view.name(topChild(view, c)->pins[0]->net), (Netlist::NetName{"u.w[1]", 1, false, {"u", "w"}}));
}

YOSYS_NAMESPACE_END
