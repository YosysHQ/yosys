#ifndef NETVIEW_HELPERS_H
#define NETVIEW_HELPERS_H

#include <gtest/gtest.h>

#include "kernel/netview.h"
#include "kernel/newcelltypes.h"
#include "kernel/register.h"
#include "kernel/rtlil.h"

YOSYS_NAMESPACE_BEGIN

inline Module *addInv(Design *design, const std::string &name)
{
	Module *inv = design->addModule(name);
	inv->addWire(ID(A))->port_input = true;
	inv->addWire(ID(Y))->port_output = true;
	inv->fixup_ports();
	inv->set_bool_attribute(ID::blackbox);
	return inv;
}

// top: in -> u_inv0 -> d0 -> u_sub (sub: a -> i1 -> y[0], a -> i2) -> p -> u_inv2 -> out
class NetViewTest : public ::testing::Test
{
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

inline void ensurePasses()
{
	static bool registered = false;
	if (!registered) {
		Pass::init_register();
		yosys_celltypes.static_cell_types = StaticCellTypes::categories.is_known;
		registered = true;
	}
}

inline Netlist::Instance *topChild(const NetView &view, const Cell *cell) { return view.instance(cell, view.top()); }

YOSYS_NAMESPACE_END

#endif
