#include "netviewHelpers.h"

YOSYS_NAMESPACE_BEGIN

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
	for (const Netlist::NetName &alias : view.aliases(zero))
		found = found || alias.wire == "tie";
	EXPECT_TRUE(found);
	EXPECT_EQ(topChild(view, u_x)->pins[0]->net, nullptr);
	Netlist::Net *d0_net = topChild(view, u_inv0)->pins[1]->net;
	EXPECT_EQ(d0_net, topChild(view, u_sub)->pins[0]->net);
	EXPECT_EQ(d0_net->pins.size(), 2u);
	EXPECT_EQ(view.name(d0_net), (Netlist::NetName{"d0", 0, true}));
	EXPECT_FALSE(view.nets(t).empty());
	EXPECT_EQ(view.nets(topChild(view, u_inv0)).size(), 0u); // leaves own none
	EXPECT_EQ(topChild(view, u_sub)->findPin("y", 1)->hdlIndex(), 2); // y[0:3] holds y[2] at offset 1
}

// write_verilog sorts the design, opt_clean reorders the connections
TEST_F(NetViewTest, topIsNoRegisterOrBuffer)
{
	NetView view;
	view.build(d);
	EXPECT_FALSE(view.isRegister(view.top()));
	EXPECT_FALSE(view.isBuffer(view.top()));
	EXPECT_FALSE(view.isClockPin(view.top()->pins[0]));
}

// top: w <- u_bidi.io (bidi: io <- g)
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

TEST_F(NetViewTest, deletedDesignMakesTheViewStale)
{
	std::shared_ptr<Design> other = std::make_shared<Design>();
	Module *m = other->addModule(ID(top));
	m->addWire(ID(a))->port_input = true;
	m->fixup_ports();
	NetView view;
	view.build(other.get());
	EXPECT_TRUE(view.upToDate());
	other.reset();
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

// u_$x is a legal Verilog name, the default '.' separates first
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

struct NoCellLibrary : Netlist::CellLibrary {
	bool ports(const Netlist::Instance &, std::vector<Netlist::Port> &) override { return false; }
};

TEST_F(NetViewTest, unknownTypeWithALibraryIsAnErrorIfConnected)
{
	top->addCell("\\u_tap0", "\\TAP");
	NoCellLibrary library;
	NetView view;
	view.build(d, {&library});
	EXPECT_TRUE(topChild(view, top->cell("\\u_tap0"))->pins.empty());

	view.clear();
	top->addCell("\\u_tap1", "\\TAP")->setPort("\\A", in);
	auto scope = logger().error_throw_scope();
	EXPECT_THROW(view.build(d, {&library}), log_cmd_error_exception);
	EXPECT_FALSE(view.built());
}

// $pre -> $barrier -> d0
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

// a protected load pin of a constant: c -> $barrier -> post -> u_inv2
// x on A makes no net, Y keeps its own
// literal 1 on A: 1 -> $barrier -> post -> u_inv2
TEST_F(NetViewTest, barrierFromALiteralConstantIsConstant)
{
	Wire *post = top->addWire("$post");
	top->addBarrier("$b", State::S1, post);
	u_inv2->setPort(ID(A), post);
	NetView view;
	view.build(d);
	EXPECT_EQ(topChild(view, u_inv2)->pins[0]->net->constant, Netlist::Net::Const::One);
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

TEST_F(NetViewTest, childNamesAreUniqueInTheScope)
{
	Cell *k = top->addCell("\\k", ID(INV));
	k->set_hdlname_attribute({"u", "x"});
	Cell *b = top->addCell("\\b", ID(INV));
	b->set_hdlname_attribute({"u", "x"});
	Cell *r = top->addCell("\\r", ID(INV));
	r->set_hdlname_attribute({"k"});
	Cell *v = top->addCell("\\v", ID(INV));
	v->set_hdlname_attribute({"v", "y"});
	NetView view;
	view.build(d);
	dict<const Cell *, std::string> by_cell;
	for (const Netlist::Instance *child : view.top()->children)
		by_cell[view.cell(child)] = child->unique_name;
	EXPECT_EQ(by_cell.at(k), "k");
	EXPECT_EQ(by_cell.at(b), "b");
	EXPECT_EQ(by_cell.at(r), "r");
	EXPECT_EQ(by_cell.at(v), "v/y");
	EXPECT_EQ(by_cell.at(u_sub), "u_sub");
}

TEST_F(NetViewTest, bodyKeysAreEqualForEqualBodies)
{
	addWrapper(d, "\\S1", "\\i", "\\INV", false)->set_string_attribute(ID::hdlname, "S");
	addWrapper(d, "\\S2", "\\i", "\\INV", false)->set_string_attribute(ID::hdlname, "S");
	addWrapper(d, "\\S3", "\\j", "\\INV", false)->set_string_attribute(ID::hdlname, "S");
	addWrapper(d, "\\W1", "\\c", "\\S1", false)->set_string_attribute(ID::hdlname, "W");
	addWrapper(d, "\\W2", "\\c", "\\S3", false)->set_string_attribute(ID::hdlname, "W");
	addWrapper(d, "\\W3", "\\c", "\\S2", false)->set_string_attribute(ID::hdlname, "W");
	std::vector<Cell *> wrappers;
	for (int n = 1; n <= 3; n++) {
		Cell *cell = top->addCell(stringf("\\w%d", n), stringf("\\W%d", n));
		cell->setPort(ID(a), in);
		wrappers.push_back(cell);
	}
	NetView view;
	view.build(d);
	std::vector<uint64_t> keys;
	std::vector<uint64_t> child_keys;
	for (Cell *cell : wrappers) {
		Netlist::Instance *scope = topChild(view, cell);
		keys.push_back(view.bodyKey(scope));
		child_keys.push_back(view.bodyKey(scope->children.at(0)));
	}
	EXPECT_EQ(child_keys[0], child_keys[2]);
	EXPECT_NE(child_keys[0], child_keys[1]);
	EXPECT_EQ(keys[0], keys[2]);
	EXPECT_NE(keys[0], keys[1]); // only the body of c differs
}

static bool idsFit(int mids, bool pins, std::string &reason)
{
	Design design;
	Module *leaf = design.addModule("\\leaf");
	Wire *wide = leaf->addWire("\\w", 65536);
	if (pins) {
		wide->port_input = true;
		leaf->fixup_ports();
		leaf->set_bool_attribute(ID::blackbox);
	}
	Module *mid = design.addModule("\\mid");
	for (int n = 0; n < 256; n++)
		mid->addCell(stringf("\\l%d", n), "\\leaf");
	Module *m = design.addModule(ID(top));
	m->set_bool_attribute(ID::top);
	for (int n = 0; n < mids; n++)
		m->addCell(stringf("\\m%d", n), "\\mid");
	return NetView::buildable(&design, reason);
}

TEST(NetViewBuildableTest, buildableRefusesPinAndNetIdOverflow)
{
	for (bool pins : {true, false}) {
		std::string reason;
		EXPECT_TRUE(idsFit(255, pins, reason)) << reason;
		EXPECT_FALSE(idsFit(256, pins, reason)) << pins;
		EXPECT_NE(reason.find("32-bit"), std::string::npos) << reason;
	}
}
YOSYS_NAMESPACE_END
