#include "netviewHelpers.h"

YOSYS_NAMESPACE_BEGIN

TEST_F(NetViewTest, namesAndConstants)
{
	Cell *u_x = top->addCell("\\u_x", ID(INV));
	u_x->setPort(ID(A), State::Sx);
	NetView view(d);
	Netlist::Instance *t = view.top();
	std::vector<const Netlist::Net *> zeros;
	for (const Netlist::Net &net : view.nets()) {
		EXPECT_NE(net.constant, Netlist::Net::Const::One);
		if (net.constant == Netlist::Net::Const::Zero)
			zeros.push_back(&net);
	}
	ASSERT_EQ(zeros.size(), 1u);
	const Netlist::Net *zero = zeros[0];
	EXPECT_EQ(zero->scope, t);
	EXPECT_EQ(topChild(view, u_x)->pins[0]->net, nullptr);
	Netlist::Net *d0_net = topChild(view, u_inv0)->pins[1]->net;
	EXPECT_EQ(d0_net, topChild(view, u_sub)->pins[0]->net);
	EXPECT_EQ(d0_net->pins.size(), 2u);
	EXPECT_EQ(d0_net->name, (Netlist::NetName{"d0", 0, true}));
	EXPECT_FALSE(t->nets.empty());
	EXPECT_EQ(topChild(view, u_inv0)->nets.size(), 0u); // a leaf owns no nets, its pins are on the nets of its parent
	EXPECT_EQ(topChild(view, u_sub)->findPin("y", 1)->hdlIndex(), 2); // y counts 0 up to 3, offset 1 holds y[2]
}

TEST_F(NetViewTest, yosysCellTypesGiveTheTypeFacts)
{
	ensurePasses(); // the cell types come with yosys_setup
	Cell *flop = top->addCell("\\flop", ID($_DFF_P_));
	flop->setPort(ID::C, in);
	flop->setPort(ID::D, d0);
	flop->setPort(ID::Q, top->addWire("\\flop_q"));
	Cell *buffer = top->addCell("\\buffer", ID($_BUF_));
	buffer->setPort(ID::A, in);
	buffer->setPort(ID::Y, top->addWire("\\buffer_y"));
	NetView view(d);
	const Netlist::Instance *flop_inst = topChild(view, flop);
	EXPECT_FALSE(flop_inst->type->is_buffer);
	EXPECT_TRUE(topChild(view, buffer)->type->is_buffer);
	EXPECT_FALSE(view.top()->type->is_buffer);
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

TEST_F(NetViewTest, deletedDesignMakesTheViewStale)
{
	std::shared_ptr<Design> other = std::make_shared<Design>();
	Module *m = other->addModule(ID(top));
	m->addWire(ID(a))->port_input = true;
	m->fixup_ports();
	NetView view(other.get());
	EXPECT_TRUE(view.upToDate());
	other.reset();
	EXPECT_FALSE(view.upToDate());
}

TEST_F(NetViewTest, buildableRefusesRangeOverflow)
{
	std::string reason;
	top->addWire("\\huge", 2)->start_offset = INT_MAX - 1; // fits, the range is INT_MAX down to INT_MAX-1
	ASSERT_TRUE(NetView::buildable(d, reason)) << reason;
	top->wire("\\huge")->start_offset = INT_MAX;
	EXPECT_FALSE(NetView::buildable(d, reason));
	EXPECT_NE(reason.find("huge"), std::string::npos) << reason;
	top->remove(pool<Wire *>{top->wire("\\huge")});
	ASSERT_TRUE(NetView::buildable(d, reason)) << reason;
	inv->addWire(ID(B), 2)->start_offset = INT_MAX; // the range is INT_MAX+1 down to INT_MAX
	inv->wire(ID(B))->port_input = true;
	inv->fixup_ports();
	EXPECT_FALSE(NetView::buildable(d, reason));
	EXPECT_NE(reason.find("INV"), std::string::npos) << reason;
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
	NetView view(&design);
	Netlist::Instance *iu = topChild(view, u);
	EXPECT_EQ(iu->name, "$u");
	const std::vector<Netlist::Port> &top_ports = view.top()->type->ports;
	ASSERT_EQ(top_ports.size(), 2u);
	EXPECT_TRUE(top_ports[0].name == "1in" || top_ports[1].name == "1in");
	ASSERT_EQ(iu->pins.size(), 3u);
	for (Netlist::Pin *pin : iu->pins) {
		const std::string &port = pin->port().name;
		EXPECT_TRUE(port == "$a" || port == "$p" || port == "Y") << port;
		ASSERT_NE(pin->net, nullptr) << port;
		EXPECT_EQ(pin->net->name.wire, port == "Y" ? "o" : "1in") << port;
	}
}

struct NoCellLibrary : Netlist::CellLibrary {
	bool describe(Netlist::CellType &) override { return false; }
};

TEST_F(NetViewTest, unknownTypeWithALibraryIsAnErrorIfConnected)
{
	top->addCell("\\u_tap0", "\\TAP");
	NoCellLibrary library;
	NetView view(d, {&library});
	EXPECT_TRUE(topChild(view, top->cell("\\u_tap0"))->pins.empty());

	top->addCell("\\u_tap1", "\\TAP")->setPort("\\A", in);
	auto scope = logger().error_throw_scope();
	EXPECT_THROW(NetView failed(d, {&library}), log_cmd_error_exception);
}

// $pre -> $connect -> d0
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
	NetView view(d);
	EXPECT_EQ(topChild(view, connect), nullptr);
	EXPECT_EQ(topChild(view, input), nullptr);
	EXPECT_EQ(view.top()->children.size(), 3u);
	Netlist::Net *driven = topChild(view, u_inv0)->pins[1]->net;
	EXPECT_EQ(driven, topChild(view, u_sub)->pins[0]->net);
}

// a literal 1 on A, 1 -> $barrier -> post -> u_inv2
TEST_F(NetViewTest, barrierFromALiteralConstantIsConstant)
{
	Wire *post = top->addWire("$post");
	top->addBarrier("$b", State::S1, post);
	u_inv2->setPort(ID(A), post);
	NetView view(d);
	EXPECT_EQ(topChild(view, u_inv2)->pins[0]->net->constant, Netlist::Net::Const::One);
}

static Module *addWrapper(Design *design, const std::string &name, const std::string &child, const std::string &type)
{
	Module *module = design->addModule(name);
	Wire *a = module->addWire(ID(a));
	a->port_input = true;
	Wire *y = module->addWire(ID(y));
	y->port_output = true;
	module->fixup_ports();
	Cell *cell = module->addCell(child, type);
	cell->setPort(type == "\\INV" ? ID(A) : ID(a), a);
	cell->setPort(type == "\\INV" ? ID(Y) : ID(y), y);
	return module;
}

TEST_F(NetViewTest, bodyKeysAreEqualForEqualBodies)
{
	addWrapper(d, "\\S1", "\\i", "\\INV")->set_string_attribute(ID::hdlname, "S");
	addWrapper(d, "\\S2", "\\i", "\\INV")->set_string_attribute(ID::hdlname, "S");
	addWrapper(d, "\\S3", "\\j", "\\INV")->set_string_attribute(ID::hdlname, "S");
	addWrapper(d, "\\W1", "\\c", "\\S1")->set_string_attribute(ID::hdlname, "W");
	addWrapper(d, "\\W2", "\\c", "\\S3")->set_string_attribute(ID::hdlname, "W");
	addWrapper(d, "\\W3", "\\c", "\\S2")->set_string_attribute(ID::hdlname, "W");
	std::vector<Cell *> wrappers;
	for (int n = 1; n <= 3; n++) {
		Cell *cell = top->addCell(stringf("\\w%d", n), stringf("\\W%d", n));
		cell->setPort(ID(a), in);
		wrappers.push_back(cell);
	}
	NetView view(d);
	std::vector<uint64_t> keys;
	std::vector<uint64_t> child_keys;
	for (Cell *cell : wrappers) {
		Netlist::Instance *scope = topChild(view, cell);
		keys.push_back(scope->type->body_key);
		child_keys.push_back(scope->children.at(0)->type->body_key);
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
