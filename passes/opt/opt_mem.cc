/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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

#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/mem.h"
#include "kernel/ff.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct OptMemPass : public Pass {
	OptMemPass() : Pass("opt_mem", "optimize memories") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_mem [options] [selection]\n");
		log("\n");
		log("This pass performs various optimizations on memories in the design.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing OPT_MEM pass (optimize memories).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			// if (args[argidx] == "-nomux") {
			// 	mode_nomux = true;
			// 	continue;
			// }
			break;
		}
		extra_args(args, argidx, design);

		int total_count = 0;
		for (auto module : design->selected_modules()) {
			if (module->has_processes_warn())
				continue;

			SigMap sigmap(module);
			FfInitVals initvals(&sigmap, module);
			for (auto &mem : Mem::get_selected_memories(module)) {
				std::vector<bool> always_0(mem.width, true);
				std::vector<bool> always_1(mem.width, true);
				bool changed = false;
				for (auto &port : mem.wr_ports) {
					if (port.en.is_fully_zero()) {
						port.removed = true;
						changed = true;
						total_count++;
					} else {
						for (int sub = 0; sub < (1 << port.wide_log2); sub++) {
							for (int i = 0; i < mem.width; i++) {
								int bit = sub * mem.width + i;
								if (port.en[bit] != State::S0) {
									if (port.data[bit] != State::Sx && port.data[bit] != State::S0) {
										always_0[i] = false;
									}
									if (port.data[bit] != State::Sx && port.data[bit] != State::S1) {
										always_1[i] = false;
									}
								} else {
									if (port.data[bit] != State::Sx) {
										port.data[bit] = State::Sx;
										changed = true;
										total_count++;
									}
								}
							}
						}
					}
				}
				for (auto &init : mem.inits) {
					for (int i = 0; i < GetSize(init.data); i++) {
						State bit = init.data.bits[i];
						int lane = i % mem.width;
						if (bit != State::Sx && bit != State::S0) {
							always_0[lane] = false;
						}
						if (bit != State::Sx && bit != State::S1) {
							always_1[lane] = false;
						}
					}
				}
				std::vector<int> swizzle;
				for (int i = 0; i < mem.width; i++) {
					if (!always_0[i] && !always_1[i]) {
						swizzle.push_back(i);
						continue;
					}
					State bit;
					if (!always_0[i]) {
						log("%s.%s: removing const-1 lane %d\n", log_id(module->name), log_id(mem.memid), i);
						bit = State::S1;
					} else if (!always_1[i]) {
						log("%s.%s: removing const-0 lane %d\n", log_id(module->name), log_id(mem.memid), i);
						bit = State::S0;
					} else {
						log("%s.%s: removing const-x lane %d\n", log_id(module->name), log_id(mem.memid), i);
						bit = State::Sx;
					}
					// Reconnect read port data.
					for (auto &port: mem.rd_ports) {
						for (int sub = 0; sub < (1 << port.wide_log2); sub++) {
							int bidx = sub * mem.width + i;
							if (!port.clk_enable) {
								module->connect(port.data[bidx], bit);
							} else {
								// The FF will most likely be redundant, but it's up to opt_dff to deal with this.
								FfData ff(module, &initvals, NEW_ID);
								ff.width = 1;
								ff.has_clk = true;
								ff.sig_clk = port.clk;
								ff.pol_clk = port.clk_polarity;
								if (port.en != State::S1) {
									ff.has_ce = true;
									ff.pol_ce = true;
									ff.sig_ce = port.en;
								}
								if (port.arst != State::S0) {
									ff.has_arst = true;
									ff.pol_arst = true;
									ff.sig_arst = port.arst;
									ff.val_arst = port.arst_value[bidx];
								}
								if (port.srst != State::S0) {
									ff.has_srst = true;
									ff.pol_srst = true;
									ff.sig_srst = port.srst;
									ff.val_srst = port.srst_value[bidx];
								}
								ff.sig_d = bit;
								ff.sig_q = port.data[bidx];
								ff.val_init = port.init_value[bidx];
								ff.emit();
							}
						}
					}
				}
				if (GetSize(swizzle) == 0) {
					mem.remove();
					total_count++;
					continue;
				}
				if (GetSize(swizzle) != mem.width) {
					for (auto &port: mem.wr_ports) {
						SigSpec new_data;
						SigSpec new_en;
						for (int sub = 0; sub < (1 << port.wide_log2); sub++) {
							for (auto i: swizzle) {
								new_data.append(port.data[sub * mem.width + i]);
								new_en.append(port.en[sub * mem.width + i]);
							}
						}
						port.data = new_data;
						port.en = new_en;
					}
					for (auto &port: mem.rd_ports) {
						SigSpec new_data;
						Const new_init;
						Const new_arst;
						Const new_srst;
						for (int sub = 0; sub < (1 << port.wide_log2); sub++) {
							for (auto i: swizzle) {
								int bidx = sub * mem.width + i;
								new_data.append(port.data[bidx]);
								new_init.bits.push_back(port.init_value.bits[bidx]);
								new_arst.bits.push_back(port.arst_value.bits[bidx]);
								new_srst.bits.push_back(port.srst_value.bits[bidx]);
							}
						}
						port.data = new_data;
						port.init_value = new_init;
						port.arst_value = new_arst;
						port.srst_value = new_srst;
					}
					for (auto &init: mem.inits) {
						Const new_data;
						Const new_en;
						for (int s = 0; s < GetSize(init.data); s += mem.width) {
							for (auto i: swizzle) {
								new_data.bits.push_back(init.data.bits[s + i]);
							}
						}
						for (auto i: swizzle) {
							new_en.bits.push_back(init.en.bits[i]);
						}
						init.data = new_data;
						init.en = new_en;
					}
					mem.width = GetSize(swizzle);
					changed = true;
					total_count++;
				}
				if (changed) {
					mem.emit();
				}
			}
		}

		if (total_count)
			design->scratchpad_set_bool("opt.did_something", true);
		log("Performed a total of %d transformations.\n", total_count);
	}
} OptMemPass;

PRIVATE_NAMESPACE_END
