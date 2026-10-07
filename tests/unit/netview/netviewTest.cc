#include <gtest/gtest.h>

#include "kernel/netview.h"
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
	EXPECT_EQ(view.top()->children[0]->id, 1u);
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

YOSYS_NAMESPACE_END
