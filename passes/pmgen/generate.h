/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
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

#ifndef PMGEN_GENERATE
#define PMGEN_GENERATE

#define GENERATE_PATTERN(pmclass, pattern) \
	generate_pattern<pmclass>([](pmclass &pm, std::function<void()> f){ return pm.run_ ## pattern(f); }, #pmclass, #pattern, design)

void pmtest_addports(Module *module)
{
	pool<SigBit> driven_bits, used_bits;
	SigMap sigmap(module);
	int icnt = 0, ocnt = 0;

	for (auto cell : module->cells())
	for (auto conn : cell->connections())
	{
		if (cell->input(conn.first))
			for (auto bit : sigmap(conn.second))
				used_bits.insert(bit);
		if (cell->output(conn.first))
			for (auto bit : sigmap(conn.second))
				driven_bits.insert(bit);
	}

	for (auto wire : vector<Wire*>(module->wires()))
	{
		SigSpec ibits, obits;
		for (auto bit : sigmap(wire)) {
			if (!used_bits.count(bit))
				obits.append(bit);
			if (!driven_bits.count(bit))
				ibits.append(bit);
		}
		if (!ibits.empty()) {
			Wire *w = module->addWire(stringf("\\i%d", icnt++), GetSize(ibits));
			w->port_input = true;
			module->connect(ibits, w);
		}
		if (!obits.empty()) {
			Wire *w = module->addWire(stringf("\\o%d", ocnt++), GetSize(obits));
			w->port_output = true;
			module->connect(w, obits);
		}
	}

	module->fixup_ports();
}

template <class pm>
void generate_pattern(std::function<void(pm&,std::function<void()>)> run, const char *pmclass, const char *pattern, Design *design)
{
	log("Generating \"%s\" patterns for pattern matcher \"%s\".\n", pattern, pmclass);

	int modcnt = 0;
	int maxmodcnt = 100;
	int maxsubcnt = 4;
	int timeout = 0;
	vector<Module*> mods;

	while (modcnt < maxmodcnt)
	{
		int submodcnt = 0, itercnt = 0, cellcnt = 0;
		Module *mod = design->addModule(NEW_ID);

		while (modcnt < maxmodcnt && submodcnt < maxsubcnt && itercnt++ < 1000)
		{
			if (timeout++ > 10000)
				log_error("pmgen generator is stuck: 10000 iterations with no matching module generated.\n");

			pm matcher(mod, mod->cells());

			matcher.rng(1);
			matcher.rngseed += modcnt;
			matcher.rng(1);
			matcher.rngseed += submodcnt;
			matcher.rng(1);
			matcher.rngseed += itercnt;
			matcher.rng(1);
			matcher.rngseed += cellcnt;
			matcher.rng(1);

			if (GetSize(mod->cells()) != cellcnt)
			{
				bool found_match = false;
				run(matcher, [&](){ found_match = true; });
				cellcnt = GetSize(mod->cells());

				if (found_match) {
					Module *m = design->addModule(stringf("\\pmtest_%s_%s_%05d",
							pmclass, pattern, modcnt++));
					log("Creating module %s with %d cells.\n", log_id(m), cellcnt);
					mod->cloneInto(m);
					pmtest_addports(m);
					mods.push_back(m);
					submodcnt++;
					timeout = 0;
				}
			}

			matcher.generate_mode = true;
			run(matcher, [](){});
		}

		if (submodcnt && maxsubcnt < (1 << 16))
			maxsubcnt *= 2;

		design->remove(mod);
	}

	Module *m = design->addModule(stringf("\\pmtest_%s_%s", pmclass, pattern));
	log("Creating module %s with %d cells.\n", log_id(m), GetSize(mods));
	for (auto mod : mods) {
		Cell *c = m->addCell(mod->name, mod->name);
		for (auto port : mod->ports) {
			Wire *w = m->addWire(NEW_ID, GetSize(mod->wire(port)));
			c->setPort(port, w);
		}
	}
	pmtest_addports(m);
}

#endif
