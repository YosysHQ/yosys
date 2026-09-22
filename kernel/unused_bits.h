#ifndef UNUSED_BITS_H
#define UNUSED_BITS_H

#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/newcelltypes.h"

YOSYS_NAMESPACE_BEGIN

struct UnusedBits
{
	SigMap sigmap;
	pool<RTLIL::SigBit> used;

	UnusedBits(RTLIL::Module *module) : sigmap(module)
	{
		NewCellTypes ct(module->design);
		collect_used(module, ct);
	}

	UnusedBits(RTLIL::Module *module, const NewCellTypes &ct) : sigmap(module)
	{
		collect_used(module, ct);
	}

	void collect_used(RTLIL::Module *module, const NewCellTypes &ct)
	{
		for (auto cell : module->cells())
			for (auto &conn : cell->connections())
				if (!ct.cell_output(cell->type, conn.first))
					add_used(conn.second);

		for (auto wire : module->wires())
			if (wire->port_output)
				add_used(wire);
	}

	void add_used(const RTLIL::SigSpec &sig)
	{
		for (auto bit : sigmap(sig))
			if (bit.wire != nullptr)
				used.insert(bit);
	}

	bool check(RTLIL::SigBit bit) const
	{
		RTLIL::SigBit mapped = sigmap(bit);
		return mapped.wire != nullptr && !used.count(mapped);
	}
};

YOSYS_NAMESPACE_END

#endif
