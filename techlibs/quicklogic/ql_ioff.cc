#include "kernel/log.h"
#include "kernel/modtools.h"
#include "kernel/register.h"
#include "kernel/rtlil.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct QlIoffPass : public Pass {
	QlIoffPass() : Pass("ql_ioff", "Infer I/O FFs for qlf_k6n10f architecture") {}

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    ql_ioff [selection]\n");
		log("\n");
		log("This pass promotes qlf_k6n10f registers directly connected to a top-level I/O\n");
		log("port to I/O FFs.\n");
		log("\n");
	}

	void execute(std::vector<std::string>, RTLIL::Design *design) override
	{
		log_header(design, "Executing QL_IOFF pass.\n");

		// TODO Disabled signorm because swap_names breaks fanout logic
		design->sigNormalize(false);

		ModWalker modwalker(design);
		Module *module = design->top_module();
		if (!module)
			return;
		modwalker.setup(module);
		pool<RTLIL::Cell *> input_ffs;
		dict<RTLIL::Wire *, std::vector<Cell*>> output_ffs;
		dict<SigBit, pool<SigBit>> output_bit_aliases;

		for (Wire* wire : module->wires())
			if (wire->port_output) {
				output_ffs[wire].resize(wire->width, nullptr);
				for (SigBit bit : SigSpec(wire))
					output_bit_aliases[modwalker.sigmap(bit)].insert(bit);
			}

		for (auto cell : module->selected_cells()) {
			if (cell->type.in(ID(dffsre), ID(sdffsre))) {
				log_debug("Checking cell %s.\n", cell->name);
				bool e_const = cell->getPort(TW::E).is_fully_ones();
				bool r_const = cell->getPort(TW::R).is_fully_ones();
				bool s_const = cell->getPort(TW::S).is_fully_ones();

				if (!(e_const && r_const && s_const)) {
					log_debug("not promoting: E, R, or S is used\n");
					continue;
				}

				SigSpec d = cell->getPort(TW::D);
				log_assert(GetSize(d) == 1);
				if (modwalker.has_inputs(d)) {
					log_debug("Cell %s is potentially eligible for promotion to input IOFF.\n", cell->name);
					// check that d_sig has no other consumers
					pool<ModWalker::PortBit> portbits;
					modwalker.get_consumers(portbits, d);
					if (GetSize(portbits) > 1) {
						log_debug("not promoting: D has other consumers\n");
						continue;
					}
					input_ffs.insert(cell);
					continue; // prefer input FFs over output FFs
				}

				SigSpec q = cell->getPort(TW::Q);
				log_assert(GetSize(q) == 1);
				if (modwalker.has_outputs(q) && !modwalker.has_consumers(q)) {
					log_debug("Cell %s is potentially eligible for promotion to output IOFF.\n", cell->name);
					for (SigBit bit : output_bit_aliases[modwalker.sigmap(q)]) {
						log_assert(bit.is_wire());
						output_ffs[bit.wire][bit.offset] = cell;
					}

				}
			}
		}

		for (auto cell : input_ffs) {
			log("Promoting register %s to input IOFF.\n", log_signal(cell->getPort(TW::Q)));
			cell->type_impl = TW::dff;
			cell->unsetPort(TW::E);
			cell->unsetPort(TW::R);
			cell->unsetPort(TW::S);
		}
		for (auto & [old_port_output, ioff_cells] : output_ffs) {
			if (std::any_of(ioff_cells.begin(), ioff_cells.end(), [](Cell * c) { return c != nullptr; }))
			{
				// create replacement output wire
				RTLIL::Wire* new_port_output = module->addWire(NEW_TWINE, old_port_output->width);
				new_port_output->start_offset = old_port_output->start_offset;
				module->swap_names(old_port_output, new_port_output);
				std::swap(old_port_output->port_id, new_port_output->port_id);
				std::swap(old_port_output->port_input, new_port_output->port_input);
				std::swap(old_port_output->port_output, new_port_output->port_output);
				std::swap(old_port_output->upto, new_port_output->upto);
				std::swap(old_port_output->is_signed, new_port_output->is_signed);
				std::swap(old_port_output->attributes, new_port_output->attributes);

				// create new output FFs
				SigSpec sig_o(old_port_output);
				SigSpec sig_n(new_port_output);
				for (int i = 0; i < new_port_output->width; i++) {
					if (ioff_cells[i]) {
						log("Promoting %s to output IOFF.\n", log_signal(sig_n[i]));

						RTLIL::Cell *new_cell = module->addCell(NEW_TWINE, TW::dff);
						new_cell->setPort(TW::C, ioff_cells[i]->getPort(TW::C));
						new_cell->setPort(TW::D, ioff_cells[i]->getPort(TW::D));
						new_cell->setPort(TW::Q, sig_n[i]);
						new_cell->set_bool_attribute(ID::keep);
					} else {
						module->connect(sig_n[i], sig_o[i]);
					}
				}
			}
		}
	}
} QlIoffPass;

PRIVATE_NAMESPACE_END
