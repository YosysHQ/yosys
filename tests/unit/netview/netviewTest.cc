#include <gtest/gtest.h>

#include "kernel/netview.h"
#include "kernel/newcelltypes.h"
#include "kernel/register.h"
#include "kernel/rtlil.h"

YOSYS_NAMESPACE_BEGIN

static Module *addInv(Design *design, const std::string &name)
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

		inv = addInv(d, "\\INV");
		inv2 = addInv(d, "\\INV2"); // unused

		sub = d->addModule("\\sub");
		a = sub->addWire(ID(a));
		a->port_input = true;
		y = sub->addWire(ID(y), 4);
		y->port_output = true;
		y->upto = true;
		sub->fixup_ports();
		i1 = sub->addCell("\\i1", ID(INV));
		i1->setPort(ID(A), a);
		i1->setPort(ID(Y), SigBit(y, 0));
		i2 = sub->addCell("\\i2", ID(INV)); // no load
		i2->setPort(ID(A), a);

		top = d->addModule(ID(top));
		top->set_bool_attribute(ID::top);
		in = top->addWire("\\in");
		in->port_input = true;
		out = top->addWire("\\out");
		out->port_output = true;
		q = top->addWire("\\q", 4);
		q->port_input = true;
		s = top->addWire("\\s");
		s->start_offset = 5; // a scalar with an offset
		s->port_input = true;
		top->fixup_ports();
		d0 = top->addWire("\\d0");
		p = top->addWire("\\p");
		tie = top->addWire("\\tie");
		top->connect(tie, State::S0);
		u_inv0 = top->addCell("\\u_inv0", ID(INV));
		u_inv0->setPort(ID(A), in);
		u_inv0->setPort(ID(Y), d0);
		u_sub = top->addCell("\\u_sub", "\\sub");
		u_sub->setPort(ID(a), d0);
		u_sub->setPort(ID(y), SigSpec(p));
		u_inv2 = top->addCell("\\u_inv2", ID(INV));
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
	EXPECT_FALSE(t->isLeaf());
	EXPECT_EQ(view.module(t), top);
	EXPECT_EQ(t->children.size(), 3u);

	Netlist::Instance *isub = view.instance(u_sub);
	Netlist::Instance *iinv0 = view.instance(u_inv0);
	ASSERT_NE(isub, nullptr);
	EXPECT_FALSE(isub->isLeaf());
	EXPECT_TRUE(iinv0->isLeaf());
	EXPECT_NE(iinv0->kind, Netlist::Instance::Kind::InternalLeaf);
	EXPECT_EQ(isub->parent, t);
	EXPECT_EQ(view.module(isub), sub);
	EXPECT_EQ(view.scopes(sub), std::vector<Netlist::Instance *>{isub});
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
	EXPECT_EQ(view.pin(isub, "y", 0), y0);
	EXPECT_EQ(view.pin(isub, "y", 4), nullptr);
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
	EXPECT_FALSE(view.shape(qpins[0]).scalar());
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
		EXPECT_EQ(view.instance(order[i])->id, i + 1) << order[i]->name.unescape();
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
	const Netlist::Pin *pin = view.top()->pins[0];
	pin->user = 7; // a consumer writes it through a const pin
	view.reset();
	EXPECT_FALSE(view.built());
	EXPECT_FALSE(view.valid());
	EXPECT_EQ(d->monitors.count(&view), 0u);
	view.build(d);
	EXPECT_TRUE(view.valid());
	EXPECT_EQ(view.top()->pins[0]->id, 1u);
	EXPECT_EQ(view.top()->pins[0]->user, 0u);
	EXPECT_EQ(view.top()->children[0]->id, 1u);
	EXPECT_EQ(view.nets(view.top())[0]->id, 1u);
}

TEST_F(NetViewTest, retireKeepsOwners)
{
	NetView view;
	view.build(d);
	Netlist::Instance *inv = view.instance(u_inv0);
	EXPECT_FALSE(view.retire()->built());
	EXPECT_EQ(inv->netlist, &view);
	EXPECT_TRUE(inv->pins.empty());
	EXPECT_EQ(view.instance(u_inv0), nullptr);
}

TEST_F(NetViewTest, namingPrefersKeepThenShallowHdlpath)
{
	Wire *d1 = top->addWire("\\d1");
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

	sub->addProcess("\\proc");
	EXPECT_FALSE(NetView::buildable(d, reason));
	EXPECT_NE(reason.find("(run proc)"), std::string::npos) << reason;
	sub->remove(sub->processes.at(d->twines().find("\\proc")));

	Cell *u_sub2 = top->addCell("\\u_sub2", "\\sub");
	EXPECT_TRUE(NetView::buildable(d, reason)) << reason;
	top->remove(u_sub2);
	Cell *self = sub->addCell("\\self", "\\sub");
	EXPECT_FALSE(NetView::buildable(d, reason));
	EXPECT_NE(reason.find("contains itself"), std::string::npos) << reason;
	sub->remove(self);

	Design empty;
	EXPECT_FALSE(NetView::buildable(&empty, reason));
	EXPECT_NE(reason.find("no top"), std::string::npos);
}

TEST_F(NetViewTest, sharedModuleUnfolds)
{
	sub->connect(SigBit(y, 1), State::S1);
	Cell *u_sub2 = top->addCell("\\u_sub2", "\\sub");
	u_sub2->setPort(ID(a), in);
	NetView view;
	view.build(d);
	Netlist::Instance *first = view.instance(i1, view.instance(u_sub));
	Netlist::Instance *second = view.instance(i1, view.instance(u_sub2));
	ASSERT_NE(first, nullptr);
	ASSERT_NE(second, nullptr);
	EXPECT_NE(first->parent, second->parent);
	EXPECT_EQ(view.cell(first), i1);
	EXPECT_EQ(view.cell(second), i1);
	EXPECT_EQ(view.module(first->parent), sub);
	EXPECT_EQ(view.scopes(sub).size(), 2u);

	Netlist::Net *net = second->pins[0]->net;
	EXPECT_NE(first->pins[0]->net, net);
	EXPECT_EQ(net->scope, second->parent);
	EXPECT_EQ(second->parent->pins[0]->term->net, net);
	EXPECT_EQ(second->parent->pins[0]->net, view.instance(u_inv0)->pins[0]->net);
	EXPECT_EQ(view.nets(first->parent).size(), view.nets(second->parent).size());
	EXPECT_EQ(view.wireBits(first->pins[0]->net), std::vector<SigBit>{SigBit(a)});
	for (const Netlist::NetAlias &alias : view.aliases(second->parent))
		EXPECT_EQ(alias.net->scope, second->parent) << alias.name.wire;
	std::vector<Netlist::Net *> ones = view.constNets(Netlist::Net::Const::One);
	ASSERT_EQ(ones.size(), 2u);
	EXPECT_NE(ones[0]->scope, ones[1]->scope);
	for (Netlist::Net *one : ones)
		EXPECT_TRUE(one->scope == first->parent || one->scope == second->parent);

	// The instance of a cell in each scope
	EXPECT_EQ(view.instance(i1), nullptr);
	EXPECT_EQ(view.instance(i1, second->parent), second);
	EXPECT_EQ(view.instance(i1, view.top()), nullptr);
}

TEST_F(NetViewTest, selectionDoesNotMatter)
{
	NetView view;
	view.build(d);
	d->selection().select(sub);
	view.invalidateCheck();
	EXPECT_TRUE(view.valid());
}

// Stale after an edit, then rebuilt for the next
static void expectStale(NetView &view, Design *d)
{
	view.invalidateCheck();
	EXPECT_FALSE(view.valid());
	view.reset();
	view.build(d);
	EXPECT_TRUE(view.valid());
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
	Netlist::Net *d0_net = view.instance(u_inv0)->pins[1]->net;
	top->rename(d0, "\\renamed");
	top->remove(pool<Wire *>{d0});
	view.invalidateCheck();
	EXPECT_FALSE(view.valid());
	EXPECT_EQ(view.wireName(d0_net), (Netlist::NetName{"d0", 0, true}));
}

TEST_F(NetViewTest, monitorEventsMakeTheViewStale)
{
	NetView view;
	view.build(d);
	u_inv2->setPort(ID(A), in);
	EXPECT_FALSE(view.valid());

	NetView other;
	other.build(d);
	top->connect(p, d0);
	EXPECT_FALSE(other.valid());

	NetView third;
	third.build(d);
	d->addModule("\\extra");
	EXPECT_FALSE(third.valid());
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
	view.invalidateCheck();
	EXPECT_FALSE(view.valid());
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
	EXPECT_EQ(view.instance(top->cell("\\u1")), nullptr);
	EXPECT_EQ(view.top()->children.size(), 2u); // u1.i0, u1.u2.j
	delete design;
}

TEST(NetViewFlatTest, hdlnameBecomesHdlpath)
{
	Design *design = flatDesign();
	Module *top = design->module(ID(top));
	NetView view;
	view.build(design);
	Netlist::Instance *i0 = view.instance(top->cell("\\u1.i0"));
	Netlist::Instance *j = view.instance(top->cell("\\u1.u2.j"));
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
	EXPECT_EQ(view.wireName(y), (Netlist::NetName{"y", 0, true}));
	Netlist::Net *a = i0->pins[0]->net;
	EXPECT_EQ(view.wireName(a), (Netlist::NetName{"a", 0, true}));
	EXPECT_EQ(view.wireName(mid), (Netlist::NetName{"u1.mid", 0, true, {"u1", "mid"}})); // also u1.u2.a
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

TEST(NetViewNameTest, flattenNamesGiveSourcePath)
{
	EXPECT_EQ(detail::flattenPath("$flatten\\u1.\\l0.$and$x.v:3$7"), (std::vector<std::string>{"u1", "l0", "$and$x.v:3$7"}));
	EXPECT_EQ(detail::flattenPath("$flatten\\u1/$y"), (std::vector<std::string>{"u1", "$y"}));
	EXPECT_EQ(detail::flattenPath("$flatten\\u1_\\l0_$y"), (std::vector<std::string>{"u1", "l0", "$y"}));
	EXPECT_TRUE(detail::flattenPath("$and$x.v:3$7").empty());
	EXPECT_TRUE(detail::flattenPath("$flatten\\u1").empty());
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
		bool bus = port == "z";
		EXPECT_EQ(view.shape(pin).scalar(), !bus) << port;
		EXPECT_EQ(view.wireName(pin->term->net).scalar, !bus) << port;
		EXPECT_EQ(view.wireName(pin->term->net).index, port == "s" ? 5 : 0);
	}
	EXPECT_EQ(buses, 2);
	EXPECT_TRUE(view.shape(view.instance(u_inv0)->pins[0]).scalar());
	EXPECT_TRUE(view.wireName(view.instance(u_inv0)->pins[1]->net).scalar);
}

TEST_F(NetViewTest, zeroWidthPortsHaveNoShape)
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
	for (const Netlist::PortShape &shape : *view.top()->ports)
		EXPECT_NE(shape.width, 0) << shape.name;
	EXPECT_EQ(view.top()->ports->size(), 4u); // in, out, q, s
	ASSERT_EQ(view.instance(u_z)->ports->size(), 1u);
	EXPECT_EQ((*view.instance(u_z)->ports)[0].name, "Y");
}

TEST_F(NetViewTest, unknownCellTypeIsACommandError)
{
	top->addCell("\\u_unknown", "\\UNKNOWN");
	auto scope = logger().error_throw_scope();
	NetView view;
	EXPECT_THROW(view.build(d), log_cmd_error_exception);
	EXPECT_FALSE(view.built());
	EXPECT_EQ(d->monitors.count(&view), 0u);
	top->remove(top->cell("\\u_unknown"));
	view.build(d);
	EXPECT_TRUE(view.valid());
}

struct NoLeafModel : Netlist::LeafModel {
	bool ports(const Netlist::Instance &, std::vector<Netlist::PortShape> &) override { return false; }
	bool isRegister(const Netlist::Instance &) override { return false; }
	bool isClockPin(const Netlist::Pin &) override { return false; }
};

TEST_F(NetViewTest, unmodeledLeafTakesTheHostPorts)
{
	NoLeafModel model;
	NetView view;
	int warnings = logger().get_warnings_total();
	view.build(d, &model);
	EXPECT_EQ(logger().get_warnings_total(), warnings + 1);
	const std::vector<Netlist::PortShape> &ports = *view.instance(u_inv0)->ports;
	ASSERT_EQ(ports.size(), 2u);
	EXPECT_EQ(ports[0].name, "A");
	EXPECT_EQ(ports[1].name, "Y");
}

TEST_F(NetViewTest, directEditsNeedInvalidateCheck)
{
	Cell *u_spare = top->addCell("\\u_spare", ID(INV)); // no connections
	NetView view;
	view.build(d);
	u_inv2->type = d->twines().add("\\INV2");
	EXPECT_TRUE(view.valid());
	view.invalidateCheck();
	EXPECT_FALSE(view.valid());
	u_inv2->type = ID(INV);
	view.invalidateCheck();
	EXPECT_FALSE(view.valid());

	view.reset();
	view.build(d);
	top->remove(u_spare);
	EXPECT_TRUE(view.valid());
	view.invalidateCheck();
	EXPECT_FALSE(view.valid());

	view.reset();
	view.build(d);
	top->rename(d0, "\\renamed");
	EXPECT_TRUE(view.valid());
	view.invalidateCheck();
	EXPECT_FALSE(view.valid());
}

// $pre -> $barrier -> d0
TEST_F(NetViewTest, barriersAreTransparent)
{
	Wire *pre = top->addWire("$pre");
	u_inv0->setPort(ID(Y), pre);
	Cell *barrier = top->addBarrier("$b", pre, d0);
	NetView view;
	view.build(d);
	EXPECT_EQ(view.instance(barrier), nullptr);
	EXPECT_EQ(view.top()->children.size(), 3u);
	Netlist::Net *driven = view.instance(u_inv0)->pins[1]->net;
	EXPECT_EQ(driven, view.instance(u_sub)->pins[0]->net);
	EXPECT_EQ(view.wireName(driven), (Netlist::NetName{"d0", 0, true}));
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
	EXPECT_EQ(view.instance(connect), nullptr);
	EXPECT_EQ(view.instance(input), nullptr);
	EXPECT_EQ(view.top()->children.size(), 3u);
	Netlist::Net *driven = view.instance(u_inv0)->pins[1]->net;
	EXPECT_EQ(driven, view.instance(u_sub)->pins[0]->net);
}

TEST_F(NetViewTest, cutWireNamesNoNet)
{
	Wire *cut = top->addWire("$cut");
	cut->set_bool_attribute(d->twines().add("\\netview_cut"));
	Wire *post = top->addWire("$post");
	u_inv0->setPort(ID(Y), cut);
	top->addBarrier("$b", cut, post);
	u_sub->setPort(ID(a), post);
	NetView view;
	view.build(d);
	Netlist::Net *driven = view.instance(u_inv0)->pins[1]->net;
	EXPECT_EQ(driven, view.instance(u_sub)->pins[0]->net);
	EXPECT_EQ(view.wireName(driven).wire, "$post");
}

TEST_F(NetViewTest, barrierOnAConstantKeepsItsNet)
{
	Wire *c = top->addWire(ID(c));
	top->connect(c, State::S1);
	Cell *barrier = top->addBarrier("$b", c, p);
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
	Wire *k = top->addWire("\\k");
	top->connect(k, State::S0);
	top->addBarrier("$b", d0, k);
	NetView view;
	view.build(d);
	Netlist::Net *net = view.instance(u_inv0)->pins[1]->net;
	EXPECT_EQ(net->constant, Netlist::Net::Const::None);
	EXPECT_EQ(view.wireName(net).wire, "d0");
}

// instances but the top, nets and pins below a scope
static void walk(const NetView &view, const Netlist::Instance *scope, std::array<size_t, 3> &counts)
{
	counts[1] += view.nets(scope).size();
	for (const Netlist::Instance *child : scope->children) {
		counts[0]++;
		counts[2] += child->pins.size();
		if (!child->isLeaf())
			walk(view, child, counts);
	}
}

TEST_F(NetViewTest, countsMatchAWalk)
{
	NetView view;
	view.build(d);
	std::array<size_t, 3> walked = {0, 0, view.top()->pins.size()};
	walk(view, view.top(), walked);
	EXPECT_EQ(view.counts(), walked);
	EXPECT_EQ(walked[0], 5u); // u_inv0, u_sub, u_inv2, i1 and i2
}

TEST_F(NetViewTest, countsOfAnUnbuiltViewAreZero)
{
	NetView view;
	EXPECT_EQ(view.counts(), (std::array<size_t, 3>{}));
	view.build(d);
	EXPECT_NE(view.counts(), (std::array<size_t, 3>{}));
	view.reset();
	EXPECT_EQ(view.counts(), (std::array<size_t, 3>{}));
}

TEST_F(NetViewTest, anchorFindsEachFoundObject)
{
	ensurePasses();
	NetView view;
	view.build(d);
	NetView::Found outer{NetView::Found::Kind::Cell}, inner{NetView::Found::Kind::Cell};
	outer.objects = {view.instance(u_inv0), view.instance(u_inv2)};
	inner.objects = {view.instance(i1), view.instance(i2)};
	view.anchor({&outer, &inner});
	Pass::call(d, "flatten");
	std::unique_ptr<NetView> next = view.retire();
	next->build(d);
	next->resolve({&outer, &inner});
	std::vector<const void *> outer_cells = {next->instance(u_inv0), next->instance(u_inv2)};
	std::vector<const void *> inner_cells = {next->instance(top->cell("\\u_sub.i1")), next->instance(top->cell("\\u_sub.i2"))};
	for (std::vector<const void *> *cells : {&outer.objects, &inner.objects, &outer_cells, &inner_cells})
		std::sort(cells->begin(), cells->end());
	EXPECT_EQ(outer.objects, outer_cells);
	EXPECT_EQ(inner.objects, inner_cells);
}

TEST_F(NetViewTest, resolveTakesItsOwnOccurrence)
{
	Cell *u_sub2 = top->addCell("\\u_sub2", "\\sub");
	u_sub2->setPort(ID(a), in);
	NetView view;
	view.build(d);
	NetView::Found ref{NetView::Found::Kind::Pin};
	ref.objects = {view.instance(i1, view.instance(u_sub2))->pins[0]};
	view.anchor({&ref});
	std::unique_ptr<NetView> next = view.retire();
	next->build(d);
	next->resolve({&ref});
	ASSERT_EQ(ref.objects.size(), 1u);
	EXPECT_EQ(static_cast<const Netlist::Pin *>(ref.objects[0])->inst->parent, next->instance(u_sub2));
	top->rename(u_sub2, "\\u_other");
	std::unique_ptr<NetView> last = next->retire();
	last->build(d);
	last->resolve({&ref});
	ASSERT_EQ(ref.objects.size(), 1u);
	EXPECT_EQ(static_cast<const Netlist::Pin *>(ref.objects[0])->inst->parent, last->instance(u_sub2));
}

TEST_F(NetViewTest, flattenCopyOfAKeptCellKeepsItsPath)
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
	NetView::Found ref{NetView::Found::Kind::Pin};
	ref.objects = {view.instance(i1, view.instance(mid->cell("\\s"), view.instance(m1)))->pins[0]};
	view.anchor({&ref});
	Pass::call(d, "flatten");
	std::unique_ptr<NetView> next = view.retire();
	next->build(d);
	next->resolve({&ref});
	ASSERT_EQ(ref.objects.size(), 1u);
	EXPECT_EQ(static_cast<const Netlist::Pin *>(ref.objects[0])->inst->parent, next->instance(top->cell("\\m1.s")));
}

TEST_F(NetViewTest, clockPinKeepsAnImage)
{
	NetView view;
	view.build(d);
	NetView::Found ref{NetView::Found::Kind::Pin};
	ref.image = true;
	ref.objects = {view.instance(u_sub)->pins[0]};
	view.protect({&ref});
	view.invalidateCheck();
	EXPECT_FALSE(view.valid());
	std::unique_ptr<NetView> next = view.retire();
	next->build(d);
	next->resolve({&ref});
	ASSERT_EQ(ref.image_a.size(), 1u);
	ASSERT_EQ(ref.image_y.size(), 1u);
	const Netlist::Pin *a = static_cast<const Netlist::Pin *>(ref.image_a[0]);
	const Netlist::Pin *y = static_cast<const Netlist::Pin *>(ref.image_y[0]);
	EXPECT_TRUE(next->isBarrier(a->inst));
	EXPECT_EQ(next->dir(a), Netlist::Dir::Input);
	EXPECT_EQ(a->net, next->instance(u_sub)->pins[0]->term->net);
	EXPECT_EQ(y->net, next->instance(i1)->pins[0]->net);
	EXPECT_NE(a->net, y->net);
	ASSERT_EQ(next->nets(a->inst).size(), 1u);
	EXPECT_EQ(a->term->net, y->term->net);
	std::vector<const void *> loads = {next->instance(i1)->pins[0], next->instance(i2)->pins[0]};
	std::sort(loads.begin(), loads.end());
	EXPECT_EQ(ref.objects, loads);
	EXPECT_TRUE(ref.inside);
	NetView::Found image{NetView::Found::Kind::Pin};
	image.objects = {a};
	next->anchor({&image});
	EXPECT_TRUE(image.image_pin);
}

TEST_F(NetViewTest, protectFindsAPinAfterFlatten)
{
	ensurePasses();
	NetView view;
	view.build(d);
	NetView::Found ref{NetView::Found::Kind::Pin}, net{NetView::Found::Kind::Net};
	ref.objects = {view.instance(i1)->pins[0]};
	net.objects = {view.instance(u_inv0)->pins[0]->net};
	view.protect({&ref, &net});
	EXPECT_TRUE(view.valid());
	Pass::call(d, "flatten");
	Cell *old = top->cell("\\u_sub.i1");
	ASSERT_NE(old, nullptr);
	Cell *renewed = top->addCell("$renewed", ID(INV));
	renewed->setPort(ID(A), old->getPort(ID(A)));
	renewed->setPort(ID(Y), old->getPort(ID(Y)));
	top->remove(old);
	std::unique_ptr<NetView> next = view.retire();
	next->build(d);
	next->resolve({&ref, &net});
	EXPECT_EQ(net.objects, std::vector<const void *>{next->instance(u_inv0)->pins[0]->net});
	ASSERT_EQ(ref.objects.size(), 1u);
	const Netlist::Pin *pin = static_cast<const Netlist::Pin *>(ref.objects[0]);
	EXPECT_EQ(next->cell(pin->inst), renewed);
	EXPECT_EQ(next->shape(pin).name, "A");
}

TEST_F(NetViewTest, unprotectKeepsTheAnchors)
{
	ensurePasses();
	NetView view;
	view.build(d);
	NetView::Found cell{NetView::Found::Kind::Cell};
	cell.objects = {view.instance(u_inv2)};
	view.protect({&cell});
	EXPECT_TRUE(u_inv2->get_bool_attribute(ID::keep));
	EXPECT_EQ(top->cells().size(), 5u); // a barrier at each pin
	EXPECT_NE(top->cell("\\netview_anchor$1"), nullptr);
	view.unprotect(d);
	EXPECT_FALSE(u_inv2->has_attribute(ID::keep));
	EXPECT_EQ(top->cells().size(), 3u);
	view.invalidateCheck();
	EXPECT_FALSE(view.valid());
	std::unique_ptr<NetView> next = view.retire();
	next->build(d);
	next->resolve({&cell});
	EXPECT_EQ(cell.objects, std::vector<const void *>{next->instance(u_inv2)});
}

TEST_F(NetViewTest, splitBitsOfAFlatVectorKeepTheirIndex)
{
	// splitnets copies the hdlname of a flat vector to each bit
	Wire *w0 = top->addWire("\\u.w[0]");
	Wire *w1 = top->addWire("\\u.w[1]");
	w1->start_offset = 1;
	w0->set_hdlname_attribute({"u", "w"});
	w1->set_hdlname_attribute({"u", "w"});
	Cell *c = top->addCell("\\c", ID(INV));
	c->setPort(ID(A), w1);
	NetView view;
	view.build(d);
	EXPECT_EQ(view.wireName(view.instance(c)->pins[0]->net), (Netlist::NetName{"u.w[1]", 1, false, {"u", "w"}}));
}

YOSYS_NAMESPACE_END
