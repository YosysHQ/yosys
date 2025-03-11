/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */

#include "kernel/rtlil.h"
#include "kernel/register.h"
#include "kernel/sigtools.h"

PRIVATE_NAMESPACE_BEGIN
USING_YOSYS_NAMESPACE

// promote dspv2_16x9x32_cfg_ports to dspv2_32x18x64_cfg_ports if need be
bool promote(Module *m, Cell *cell) {
	if (cell->type == ID(dspv2_32x18x64_cfg_ports)) {
		return false;
	} else {
		log_assert(cell->type == ID(dspv2_16x9x32_cfg_ports));
	}

	auto widen_output = [&](IdString port_name, int new_width) {
		if (!cell->hasPort(port_name))
			return;
		SigSpec port = cell->getPort(port_name);
		if (port.size() < new_width) {
			port = {m->addWire(NEW_ID, new_width - port.size()), port};
			cell->setPort(port_name, port);
		}
	};

	auto widen_input = [&](IdString port_name, int new_width) {
		if (!cell->hasPort(port_name))
			return;
		SigSpec port = cell->getPort(port_name);
		if (port.size() < new_width) {
			port.extend_u0(new_width, /* is_signed= */ true);
			cell->setPort(port_name, port);
		}
	};

	widen_output(ID(z_o), 50);
	widen_output(ID(a_cout_o), 32);
	widen_output(ID(b_cout_o), 18);
	widen_output(ID(z_cout_o), 50);

	auto uses_port = [&](IdString port_name) {
		return cell->hasPort(port_name) && !cell->getPort(port_name).is_fully_undef();
	};

	if (uses_port(ID(a_cin_i)) || uses_port(ID(b_cin_i)) || uses_port(ID(z_cin_i))) {
		log_error("Cannot promote %s (type %s) with cascading paths\n", log_id(cell), log_id(cell->type));
	}

	widen_input(ID(a_i), 32);
	widen_input(ID(b_i), 18);
	widen_input(ID(c_i), 18);
	cell->type = ID(dspv2_32x18x64_cfg_ports);
	return true;
}

bool did_something;

#include "ql_dsp_pm.h"

struct QlDspPass : Pass {
	QlDspPass() : Pass("ql_dsp", "pack into QuickLogic DSPs") {}
	void execute(std::vector<std::string> args, RTLIL::Design *d) override
	{
		log_header(d, "Executing QL_DSP pass. (pack into QuickLogic DSPs)\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			break;
		}
		extra_args(args, argidx, d);

		for (auto module : d->selected_modules()) {
			did_something = true;

			while (did_something)
			{
				// TODO: could be optimized by more reuse of the pmgen object
				did_something = false;
				{
					ql_dsp_pm pm(module, module->selected_cells());
					pm.run_ql_dsp_pack_regs();
				}
				{
					ql_dsp_pm pm(module, module->selected_cells());
					pm.run_ql_dsp_cascade();
				}
				{
					ql_dsp_pm pm(module, module->selected_cells());
					pm.run_ql_dsp_pack_regs();
				}
			}
		}
	}
} QlDspPass;

PRIVATE_NAMESPACE_END
