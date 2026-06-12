#include "kernel/compressor_tree.h"
#include "kernel/yosys.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

static void build_lcu_adder(Module *module, SigSpec a, SigSpec b, SigSpec y)
{
	int width = GetSize(y);

	SigSpec p = module->Xor(NEW_ID, a, b);
	SigSpec g = module->And(NEW_ID, a, b);

	SigSpec co = module->addWire(NEW_ID, width);
	Cell *lcu = module->addCell(NEW_ID, ID($lcu));
	lcu->setParam(ID::WIDTH, width);
	lcu->setPort(ID::P, p);
	lcu->setPort(ID::G, g);
	lcu->setPort(ID::CI, State::S0);
	lcu->setPort(ID::CO, co);

	SigSpec carry_in;
	carry_in.append(State::S0);
	carry_in.append(co.extract(0, width - 1));
	module->addXor(NEW_ID, p, carry_in, y);
}

static Module *make_module(Design *design, IdString name, int width)
{
	Module *module = design->addModule(name);

	Wire *a = module->addWire(ID(a), width);
	a->port_input = true;
	Wire *b = module->addWire(ID(b), width);
	b->port_input = true;
	Wire *y = module->addWire(ID(y), width);
	y->port_output = true;
	module->fixup_ports();

	return module;
}

struct TestKoggeStonePass : public Pass {
	TestKoggeStonePass() : Pass("test_kogge_stone", "build adders for Kogge-Stone equivalence testing") {}
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    test_kogge_stone [options]\n");
		log("\n");
		log("Build two modules implementing an unsigned 'y = a + b' adder of a given width,\n");
		log("and compare various internal Kogge-Stone adders.\n");
		log("\n");
		log("    -width N\n");
		log("        width of the operands and result (default = 16)\n");
		log("\n");
		log("    -gold name\n");
		log("        name of the $lcu-based reference module (default = gold)\n");
		log("\n");
		log("    -gate name\n");
		log("        name of the emit_kogge_stone() module (default = gate)\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, Design *design) override
	{
		int width = 16;
		IdString gold_name = ID(gold);
		IdString gate_name = ID(gate);

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-width" && argidx + 1 < args.size()) {
				width = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-gold" && argidx + 1 < args.size()) {
				gold_name = RTLIL::escape_id(args[++argidx]);
				continue;
			}
			if (args[argidx] == "-gate" && argidx + 1 < args.size()) {
				gate_name = RTLIL::escape_id(args[++argidx]);
				continue;
			}
			break;
		}
		extra_args(args, argidx, design, false);

		if (width < 1)
			log_cmd_error("Width must be at least 1.\n");

		log_header(design, "Executing TEST_KOGGE_STONE pass (width=%d).\n", width);

		Module *gold = make_module(design, gold_name, width);
		build_lcu_adder(gold, gold->wire(ID(a)), gold->wire(ID(b)), gold->wire(ID(y)));

		Module *gate = make_module(design, gate_name, width);
		CompressorTree::emit_kogge_stone(gate, gate->wire(ID(a)), gate->wire(ID(b)), gate->wire(ID(y)));
	}
} TestKoggeStonePass;

PRIVATE_NAMESPACE_END
