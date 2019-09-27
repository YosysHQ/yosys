// This is free and unencumbered software released into the public domain.
//
// Anyone is free to copy, modify, publish, use, compile, sell, or
// distribute this software, either in source code form or as a compiled
// binary, for any purpose, commercial or non-commercial, and by any
// means.

#include "kernel/yosys.h"
#include "kernel/sigtools.h"

#include <string>
#include <map>
#include <set>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// this function is called for each module in the design
static void find_stub_nets(RTLIL::Design *design, RTLIL::Module *module, bool report_bits)
{
	// use a SigMap to convert nets to a unique representation
	SigMap sigmap(module);

	// count how many times a single-bit signal is used
	std::map<RTLIL::SigBit, int> bit_usage_count;

	// count output lines for this module (needed only for summary output at the end)
	int line_count = 0;

	log("Looking for stub wires in module %s:\n", RTLIL::id2cstr(module->name));

	// For all ports on all cells
	for (auto &cell_iter : module->cells_)
	for (auto &conn : cell_iter.second->connections())
	{
		// Get the signals on the port
		// (use sigmap to get a uniqe signal name)
		RTLIL::SigSpec sig = sigmap(conn.second);

		// add each bit to bit_usage_count, unless it is a constant
		for (auto &bit : sig)
			if (bit.wire != NULL)
				bit_usage_count[bit]++;
	}

	// for each wire in the module
	for (auto &wire_iter : module->wires_)
	{
		RTLIL::Wire *wire = wire_iter.second;

		// .. but only selected wires
		if (!design->selected(module, wire))
			continue;

		// add +1 usage if this wire actually is a port
		int usage_offset = wire->port_id > 0 ? 1 : 0;

		// we will record which bits of the (possibly multi-bit) wire are stub signals
		std::set<int> stub_bits;

		// get a signal description for this wire and split it into separate bits
		RTLIL::SigSpec sig = sigmap(wire);

		// for each bit (unless it is a constant):
		// check if it is used at least two times and add to stub_bits otherwise
		for (int i = 0; i < GetSize(sig); i++)
			if (sig[i].wire != NULL && (bit_usage_count[sig[i]] + usage_offset) < 2)
				stub_bits.insert(i);

		// continue if no stub bits found
		if (stub_bits.size() == 0)
			continue;

		// report stub bits and/or stub wires, don't report single bits
		// if called with report_bits set to false.
		if (GetSize(stub_bits) == GetSize(sig)) {
			log("  found stub wire: %s\n", RTLIL::id2cstr(wire->name));
		} else {
			if (!report_bits)
				continue;
			log("  found wire with stub bits: %s [", RTLIL::id2cstr(wire->name));
			for (int bit : stub_bits)
				log("%s%d", bit == *stub_bits.begin() ? "" : ", ", bit);
			log("]\n");
		}

		// we have outputted a line, increment summary counter
		line_count++;
	}

	// report summary
	if (report_bits)
		log("  found %d stub wires or wires with stub bits.\n", line_count);
	else
		log("  found %d stub wires.\n", line_count);
}

// each pass contains a singleton object that is derived from Pass
struct StubnetsPass : public Pass {
	StubnetsPass() : Pass("stubnets") { }
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		// variables to mirror information from passed options
		bool report_bits = 0;

		log_header(design, "Executing STUBNETS pass (find stub nets).\n");

		// parse options
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			std::string arg = args[argidx];
			if (arg == "-report_bits") {
				report_bits = true;
				continue;
			}
			break;
		}

		// handle extra options (e.g. selection)
		extra_args(args, argidx, design);

		// call find_stub_nets() for each module that is either
		// selected as a whole or contains selected objects.
		for (auto &it : design->modules_)
			if (design->selected_module(it.first))
				find_stub_nets(design, it.second, report_bits);
	}
} StubnetsPass;

PRIVATE_NAMESPACE_END
