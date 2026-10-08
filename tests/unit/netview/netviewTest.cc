#include <gtest/gtest.h>

#include "kernel/netview.h"
#include "kernel/newcelltypes.h"
#include "kernel/register.h"
#include "kernel/rtlil.h"

YOSYS_NAMESPACE_BEGIN

static Module *addInv(Design *design, IdString name)
{
	Module *inv = design->addModule(name);
	inv->addWire(ID(A))->port_input = true;
	inv->addWire(ID(Y))->port_output = true;
	inv->fixup_ports();
	inv->set_bool_attribute(ID::blackbox);
	return inv;
}

class NetViewTest : public ::testing::Test {
protected:
	Design *d;
	Module *top, *sub, *inv, *inv2;
	Cell *u_inv0, *u_sub, *u_inv2, *i1, *i2;
	Wire *in, *out, *d0, *p, *tie, *q, *s, *a, *y;

	void SetUp() override
	{
		d = new Design;

		inv = addInv(d, ID(INV));
		inv2 = addInv(d, ID(INV2)); // unused

		sub = d->addModule(ID(sub));
		a = sub->addWire(ID(a));
		a->port_input = true;
		y = sub->addWire(ID(y), 4);
		y->port_output = true;
		y->upto = true;
		sub->fixup_ports();
		i1 = sub->addCell(ID(i1), ID(INV));
		i1->setPort(ID(A), a);
		i1->setPort(ID(Y), SigBit(y, 0));
		i2 = sub->addCell(ID(i2), ID(INV)); // no load
		i2->setPort(ID(A), a);

		top = d->addModule(ID(top));
		top->set_bool_attribute(ID::top);
		in = top->addWire(ID(in));
		in->port_input = true;
		out = top->addWire(ID(out));
		out->port_output = true;
		q = top->addWire(ID(q), 4);
		q->port_input = true;
		s = top->addWire(ID(s));
		s->start_offset = 5; // [5:5]
		s->port_input = true;
		top->fixup_ports();
		d0 = top->addWire(ID(d0));
		p = top->addWire(ID(p));
		tie = top->addWire(ID(tie));
		top->connect(tie, State::S0);
		u_inv0 = top->addCell(ID(u_inv0), ID(INV));
		u_inv0->setPort(ID(A), in);
		u_inv0->setPort(ID(Y), d0);
		u_sub = top->addCell(ID(u_sub), ID(sub));
		u_sub->setPort(ID(a), d0);
		u_sub->setPort(ID(y), SigSpec(p));
		u_inv2 = top->addCell(ID(u_inv2), ID(INV));
		u_inv2->setPort(ID(A), p);
		u_inv2->setPort(ID(Y), out);
	}

	void TearDown() override { delete d; }
};

static void ensurePasses()
{
	static bool registered = false;
	if (!registered) {
		// as yosys_setup
		Pass::init_register();
		yosys_celltypes.static_cell_types = StaticCellTypes::categories.is_known;
		registered = true;
	}
}

TEST_F(NetViewTest, buildsInstancesPinsNetsTerms)
{
	NetView view;
	view.build(d);
	Netlist::Instance *t = view.top();
	ASSERT_NE(t, nullptr);
	EXPECT_TRUE(view.isTop(t));
	EXPECT_EQ(t->id, 0u);
	EXPECT_EQ(t->name, "top");
	EXPECT_FALSE(t->leaf);
	EXPECT_EQ(view.module(t), top);
	EXPECT_EQ(t->children.size(), 3u);

	Netlist::Instance *isub = view.instance(u_sub);
	Netlist::Instance *iinv0 = view.instance(u_inv0);
	ASSERT_NE(isub, nullptr);
	EXPECT_FALSE(isub->leaf);
	EXPECT_TRUE(iinv0->leaf);
	EXPECT_FALSE(iinv0->internal);
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
	// shapes shared per library type
	ASSERT_EQ(iinv0->pins.size(), 2u);
	EXPECT_EQ(view.shape(iinv0->pins[0]).name, "A");
	EXPECT_EQ(view.shape(iinv0->pins[1]).name, "Y");
	EXPECT_EQ(iinv0->ports, view.instance(u_inv2)->ports);
	ASSERT_EQ(isub->pins.size(), 5u);
	Netlist::Pin *y0 = isub->pins[1];
	EXPECT_EQ(view.shape(y0).name, "y");
	EXPECT_EQ(y0->bit, 0);
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
		if (view.shape(pin).name == "q")
			qpins.push_back(pin);
		if (view.shape(pin).name == "s")
			spin = pin;
	}
	ASSERT_EQ(qpins.size(), 4u);
	EXPECT_EQ(view.hdlIndex(qpins[0]), 0);
	EXPECT_EQ(view.hdlIndex(qpins[3]), 3);
	EXPECT_FALSE(view.scalar(qpins[0]));
	ASSERT_NE(spin, nullptr);
	EXPECT_EQ(view.hdlIndex(spin), 5);
	Netlist::Instance *isub = view.instance(u_sub);
	EXPECT_EQ(view.hdlIndex(isub->pins[1]), 3); // y[0:3]: bit 0 is y[3]
	EXPECT_EQ(view.hdlIndex(isub->pins[4]), 0);
	EXPECT_EQ(view.dir(view.instance(u_inv0)->pins[0]), Netlist::Dir::Input);
	EXPECT_EQ(view.dir(view.instance(u_inv0)->pins[1]), Netlist::Dir::Output);
	EXPECT_EQ(view.dir(isub->pins[1]), Netlist::Dir::Output);
}

TEST_F(NetViewTest, namesAliasesAndConstants)
{
	Cell *u_x = top->addCell(ID(u_x), ID(INV));
	u_x->setPort(ID(A), State::Sx);
	NetView view;
	view.build(d);
	Netlist::Instance *t = view.top();
	Netlist::Net *zero = view.constNet(t, false);
	ASSERT_NE(zero, nullptr);
	EXPECT_EQ(zero->constant, Netlist::Net::Const::Zero);
	EXPECT_EQ(view.constNet(t, true), nullptr);
	bool found = false;
	for (const Netlist::Alias &alias : view.aliases(t)) {
		if (alias.name.wire == "tie")
			found = alias.net == zero;
	}
	EXPECT_TRUE(found);
	EXPECT_EQ(view.instance(u_x)->pins[0]->net, nullptr);
	Netlist::Net *d0_net = view.instance(u_inv0)->pins[1]->net;
	EXPECT_EQ(d0_net, view.instance(u_sub)->pins[0]->net);
	EXPECT_EQ(d0_net->pins.size(), 2u);
	EXPECT_EQ(view.wireName(d0_net), (Netlist::NetName{"d0", 0, true}));
	EXPECT_FALSE(view.nets(t).empty());
	EXPECT_EQ(view.nets(view.instance(u_inv0)).size(), 0u); // leaves own none
}

TEST_F(NetViewTest, driversAreTopInputsAndLeafOutputs)
{
	NetView view;
	view.build(d);
	for (Netlist::Pin *pin : view.top()->pins)
		EXPECT_EQ(view.isDriver(pin), view.shape(pin).name != "out") << view.shape(pin).name;
	Netlist::Instance *iinv0 = view.instance(u_inv0);
	EXPECT_FALSE(view.isDriver(iinv0->pins[0]));
	EXPECT_TRUE(view.isDriver(iinv0->pins[1]));
	for (Netlist::Pin *pin : view.instance(u_sub)->pins)
		EXPECT_FALSE(view.isDriver(pin));
}

TEST_F(NetViewTest, instancesFollowCreationOrderDepthFirst)
{
	NetView view;
	view.build(d);
	std::vector<Cell *> order = {u_inv0, u_sub, i1, i2, u_inv2};
	for (size_t i = 0; i < order.size(); i++)
		EXPECT_EQ(view.instance(order[i])->id, i + 1) << log_id(order[i]);
	std::vector<Netlist::Instance *> children = {view.instance(u_inv0), view.instance(u_sub), view.instance(u_inv2)};
	EXPECT_EQ(view.top()->children, children);

	// write_verilog sorts in place
	top->sort();
	view.reset();
	view.build(d);
	children = {view.instance(u_inv0), view.instance(u_inv2), view.instance(u_sub)};
	EXPECT_EQ(view.top()->children, children);
}

TEST_F(NetViewTest, resetRestartsIds)
{
	NetView view;
	view.build(d);
	view.reset();
	EXPECT_FALSE(view.built());
	EXPECT_FALSE(view.valid());
	view.build(d);
	EXPECT_TRUE(view.valid());
	EXPECT_EQ(view.top()->pins[0]->id, 1u);
	EXPECT_EQ(view.top()->children[0]->id, 1u);
	EXPECT_EQ(view.nets(view.top())[0]->id, 1u);
}

TEST_F(NetViewTest, namingPrefersKeepThenShallowHdlpath)
{
	Wire *d1 = top->addWire(ID(d1));
	top->connect(d1, d0);
	NetView view;
	view.build(d);
	ASSERT_EQ(view.wireName(view.instance(u_inv0)->pins[1]->net).wire, "d0");

	d1->set_bool_attribute(ID::keep);
	view.reset();
	view.build(d);
	EXPECT_EQ(view.wireName(view.instance(u_inv0)->pins[1]->net).wire, "d1");

	d1->attributes.erase(ID::keep);
	d0->set_hdlname_attribute({"u", "d0"});
	view.reset();
	view.build(d);
	EXPECT_EQ(view.wireName(view.instance(u_inv0)->pins[1]->net).wire, "d1");
}

// i -> u1 -> $n (pa, pb) -> u2 -> o
static Design *aliasDesign(const std::vector<IdString> &order)
{
	Design *design = new Design;
	addInv(design, ID(INV));
	Module *m = design->addModule(ID(top));
	m->set_bool_attribute(ID::top);
	for (IdString name : order)
		m->addWire(name);
	m->wire(ID(i))->port_input = true;
	m->wire(ID(o))->port_output = true;
	m->fixup_ports();
	Cell *u1 = m->addCell(ID(u1), ID(INV));
	u1->setPort(ID::A, m->wire(ID(i)));
	u1->setPort(ID::Y, m->wire(ID($n)));
	Cell *u2 = m->addCell(ID(u2), ID(INV));
	u2->setPort(ID::A, m->wire(ID($n)));
	u2->setPort(ID::Y, m->wire(ID(o)));
	m->connect(m->wire(ID(pb)), m->wire(ID($n)));
	m->connect(m->wire(ID(pa)), m->wire(ID($n)));
	return design;
}

TEST(NetViewNamingTest, namingIsIndependentOfWireOrder)
{
	std::vector<std::vector<IdString>> orders = {
		{ID(i), ID(o), ID(zz), ID(pa), ID($n), ID(pb)},
		{ID(pb), ID($n), ID(o), ID(pa), ID(i), ID(zz)},
	};
	for (const std::vector<IdString> &order : orders) {
		Design *design = aliasDesign(order);
		NetView view;
		view.build(design);
		Cell *u1 = design->module(ID(top))->cell(ID(u1));
		EXPECT_EQ(view.wireName(view.instance(u1)->pins[1]->net), (Netlist::NetName{"pa", 0, true}));
		EXPECT_EQ(view.aliases(view.top()).size(), 4u); // zz has no net
		view.reset();
		delete design;
	}
}

TEST_F(NetViewTest, buildableReasons)
{
	std::string reason;
	EXPECT_TRUE(NetView::buildable(d, reason));

	top->addCell(ID(u_sub2), ID(sub));
	EXPECT_FALSE(NetView::buildable(d, reason));
	EXPECT_NE(reason.find("uniquify"), std::string::npos);

	Design empty;
	EXPECT_FALSE(NetView::buildable(&empty, reason));
	EXPECT_NE(reason.find("no top"), std::string::npos);
}

static Module *addWrapper(Design *design, IdString name, IdString child, IdString type, bool mid_inv)
{
	Module *module = design->addModule(name);
	Wire *a = module->addWire(ID(a));
	a->port_input = true;
	Wire *y = module->addWire(ID(y));
	y->port_output = true;
	module->fixup_ports();
	Wire *in = a;
	if (mid_inv) {
		in = module->addWire(ID(mid));
		Cell *i0 = module->addCell(ID(i0), ID(INV));
		i0->setPort(ID(A), a);
		i0->setPort(ID(Y), in);
	}
	Cell *cell = module->addCell(child, type);
	cell->setPort(type == ID(INV) ? ID(A) : ID(a), in);
	cell->setPort(type == ID(INV) ? ID(Y) : ID(y), y);
	return module;
}

// top: a -> u1 (sub: a -> i0 -> mid -> u2 (inner: j)) -> y
static Design *flatDesign()
{
	ensurePasses();
	Design *design = new Design;
	addInv(design, ID(INV));
	addWrapper(design, ID(inner), ID(j), ID(INV), false);
	addWrapper(design, ID(sub), ID(u2), ID(inner), true);
	addWrapper(design, ID(top), ID(u1), ID(sub), false)->set_bool_attribute(ID::top);
	Pass::call(design, "flatten");
	return design;
}

TEST(NetViewFlatTest, scopeinfoIsTransparent)
{
	Design *design = flatDesign();
	Module *top = design->module(ID(top));
	ASSERT_NE(top->cell(ID(u1)), nullptr);
	EXPECT_EQ(top->cell(ID(u1))->type, ID($scopeinfo));
	NetView view;
	view.build(design);
	EXPECT_EQ(view.instance(top->cell(ID(u1))), nullptr);
	EXPECT_EQ(view.top()->children.size(), 2u); // u1.i0, u1.u2.j
	delete design;
}

TEST(NetViewFlatTest, hdlnameBecomesHdlpath)
{
	Design *design = flatDesign();
	Module *top = design->module(ID(top));
	NetView view;
	view.build(design);
	Netlist::Instance *i0 = view.instance(top->cell(ID(u1.i0)));
	Netlist::Instance *j = view.instance(top->cell(ID(u1.u2.j)));
	ASSERT_NE(i0, nullptr);
	ASSERT_NE(j, nullptr);
	EXPECT_EQ(i0->name, "u1.i0");
	EXPECT_EQ(i0->hdlpath, (std::vector<std::string>{"u1", "i0"}));
	EXPECT_EQ(j->hdlpath, (std::vector<std::string>{"u1", "u2", "j"}));
	Netlist::Net *mid = i0->pins[1]->net;
	bool found = false;
	for (const Netlist::Alias &alias : view.aliases(view.top())) {
		if (alias.name.wire == "u1.mid")
			found = alias.net == mid && alias.name.hdlpath == std::vector<std::string>{"u1", "mid"};
	}
	EXPECT_TRUE(found);

	Netlist::Net *y = j->pins[1]->net;
	EXPECT_EQ(view.wireName(y), (Netlist::NetName{"y", 0, true}));
	Netlist::Net *a = i0->pins[0]->net;
	EXPECT_EQ(view.wireName(a), (Netlist::NetName{"a", 0, true}));
	EXPECT_EQ(view.wireName(mid), (Netlist::NetName{"u1.mid", 0, true, {"u1", "mid"}})); // also u1.u2.a
	delete design;
}

TEST(NetViewNameTest, publicNamesAreUnescaped)
{
	Design design;
	Module *bb = design.addModule(ID(BB));
	bb->addWire(RTLIL::IdString("\\$a"))->port_input = true;
	bb->addWire(RTLIL::IdString("$p"))->port_input = true; // private
	bb->addWire(ID(Y))->port_output = true;
	bb->fixup_ports();
	bb->set_bool_attribute(ID::blackbox);
	Module *m = design.addModule(ID(top));
	m->set_bool_attribute(ID::top);
	Wire *i = m->addWire(RTLIL::IdString("\\1in"));
	i->port_input = true;
	Wire *o = m->addWire(ID(o));
	o->port_output = true;
	m->fixup_ports();
	Cell *u = m->addCell(RTLIL::IdString("\\$u"), ID(BB));
	u->setPort(RTLIL::IdString("\\$a"), i);
	u->setPort(RTLIL::IdString("$p"), i);
	u->setPort(ID(Y), o);
	NetView view;
	view.build(&design);
	Netlist::Instance *iu = view.instance(u);
	EXPECT_EQ(iu->name, "$u");
	ASSERT_EQ(view.top()->ports->size(), 2u);
	EXPECT_TRUE((*view.top()->ports)[0].name == "1in" || (*view.top()->ports)[1].name == "1in");
	ASSERT_EQ(iu->pins.size(), 3u);
	for (Netlist::Pin *pin : iu->pins) {
		const std::string &port = view.shape(pin).name;
		EXPECT_TRUE(port == "$a" || port == "$p" || port == "Y") << port;
		ASSERT_NE(pin->net, nullptr) << port;
		EXPECT_EQ(view.wireName(pin->net).wire, port == "Y" ? "o" : "1in") << port;
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
		const std::string &port = view.shape(pin).name;
		if (port != "s" && port != "z")
			continue;
		buses++;
		EXPECT_FALSE(view.scalar(pin)) << port;
		EXPECT_FALSE(view.wireName(pin->term->net).scalar) << port;
		EXPECT_EQ(view.wireName(pin->term->net).index, port == "s" ? 5 : 0);
	}
	EXPECT_EQ(buses, 2);
	EXPECT_TRUE(view.scalar(view.instance(u_inv0)->pins[0]));
	EXPECT_TRUE(view.wireName(view.instance(u_inv0)->pins[1]->net).scalar);
}

TEST_F(NetViewTest, zeroWidthPortsHaveNoShape)
{
	Wire *z = top->addWire(ID(z), 0);
	z->port_input = true;
	top->fixup_ports();
	Module *zb = d->addModule(ID(ZB));
	zb->addWire(ID(A), 0)->port_input = true;
	zb->addWire(ID(Y))->port_output = true;
	zb->fixup_ports();
	zb->set_bool_attribute(ID::blackbox);
	Cell *u_z = top->addCell(ID(u_z), ID(ZB));
	u_z->setPort(ID(Y), p);
	NetView view;
	view.build(d);
	for (const Netlist::PortShape &shape : *view.top()->ports)
		EXPECT_NE(shape.width, 0) << shape.name;
	EXPECT_EQ(view.top()->ports->size(), 4u); // in, out, q, s
	ASSERT_EQ(view.instance(u_z)->ports->size(), 1u);
	EXPECT_EQ((*view.instance(u_z)->ports)[0].name, "Y");
}

TEST_F(NetViewTest, unknownCellTypeIsACommandError)
{
	top->addCell(ID(u_unknown), ID(UNKNOWN));
	auto scope = logger().error_throw_scope();
	NetView view;
	EXPECT_THROW(view.build(d), log_cmd_error_exception);
	EXPECT_FALSE(view.built());
	top->remove(top->cell(ID(u_unknown)));
	view.build(d);
	EXPECT_TRUE(view.valid());
}

// $pre -> $barrier -> d0
TEST_F(NetViewTest, barriersAreTransparent)
{
	Wire *pre = top->addWire(ID($pre));
	u_inv0->setPort(ID(Y), pre);
	Cell *barrier = top->addBarrier(ID($b), pre, d0);
	NetView view;
	view.build(d);
	EXPECT_EQ(view.instance(barrier), nullptr);
	EXPECT_EQ(view.top()->children.size(), 3u);
	Netlist::Net *driven = view.instance(u_inv0)->pins[1]->net;
	EXPECT_EQ(driven, view.instance(u_sub)->pins[0]->net);
	EXPECT_EQ(view.wireName(driven), (Netlist::NetName{"d0", 0, true}));
	EXPECT_EQ(driven->pins.size(), 2u);
}

TEST_F(NetViewTest, barrierOnAConstantKeepsItsNet)
{
	Wire *c = top->addWire(ID(c));
	top->connect(c, State::S1);
	Cell *barrier = top->addBarrier(ID($b), c, p);
	NetView view;
	view.build(d);
	EXPECT_EQ(view.instance(barrier), nullptr);
	Netlist::Net *net = view.instance(u_inv2)->pins[0]->net;
	ASSERT_NE(net, nullptr);
	EXPECT_EQ(net->constant, Netlist::Net::Const::None);
	EXPECT_EQ(view.wireName(net).wire, "p");
	EXPECT_EQ(net->pins.size(), 2u);
}

TEST_F(NetViewTest, barrierOntoAConstantKeepsTheDrivenNet)
{
	Wire *k = top->addWire(ID(k));
	top->connect(k, State::S0);
	top->addBarrier(ID($b), d0, k);
	NetView view;
	view.build(d);
	Netlist::Net *net = view.instance(u_inv0)->pins[1]->net;
	EXPECT_EQ(net->constant, Netlist::Net::Const::None);
	EXPECT_EQ(view.wireName(net).wire, "d0");
}

YOSYS_NAMESPACE_END
