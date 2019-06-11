/* -*- c++ -*-
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

#ifndef SATGEN_ALGO_H
#define SATGEN_ALGO_H

#include "kernel/celltypes.h"
#include "kernel/rtlil.h"
#include "kernel/sigtools.h"
#include <stack>

YOSYS_NAMESPACE_BEGIN

struct DriverMap : public std::map<RTLIL::SigBit, std::pair<RTLIL::Cell *, std::set<RTLIL::SigBit>>> {
	RTLIL::Module *module;
	SigMap sigmap;

	using map_t = std::map<RTLIL::SigBit, std::pair<RTLIL::Cell *, std::set<RTLIL::SigBit>>>;

	struct DriverMapConeWireIterator : public std::iterator<std::input_iterator_tag, const RTLIL::SigBit *> {
		using set_iter_t = std::set<RTLIL::SigBit>::iterator;

		DriverMap *drvmap;
		const RTLIL::SigBit *sig;
		std::stack<std::pair<set_iter_t, set_iter_t>> dfs;

		DriverMapConeWireIterator(DriverMap *drvmap) : DriverMapConeWireIterator(drvmap, NULL) {}

		DriverMapConeWireIterator(DriverMap *drvmap, const RTLIL::SigBit *sig) : drvmap(drvmap), sig(sig) {}

		inline const RTLIL::SigBit &operator*() const { return *sig; };
		inline bool operator!=(const DriverMapConeWireIterator &other) const { return sig != other.sig; }
		inline bool operator==(const DriverMapConeWireIterator &other) const { return sig == other.sig; }
		inline void operator++()
		{
			if (drvmap->count(*sig)) {
				std::pair<RTLIL::Cell *, std::set<RTLIL::SigBit>> &drv = drvmap->at(*sig);
				dfs.push(std::make_pair(drv.second.begin(), drv.second.end()));
				sig = &(*dfs.top().first);
			} else {
				while (1) {
					auto &inputs_iter = dfs.top();

					inputs_iter.first++;
					if (inputs_iter.first != inputs_iter.second) {
						sig = &(*inputs_iter.first);
						return;
					} else {
						dfs.pop();
						if (dfs.empty()) {
							sig = NULL;
							return;
						}
					}
				}
			}
		}
	};

	struct DriverMapConeWireIterable {
		DriverMap *drvmap;
		const RTLIL::SigBit *sig;

		DriverMapConeWireIterable(DriverMap *drvmap, const RTLIL::SigBit *sig) : drvmap(drvmap), sig(sig) {}

		inline DriverMapConeWireIterator begin() { return DriverMapConeWireIterator(drvmap, sig); }
		inline DriverMapConeWireIterator end() { return DriverMapConeWireIterator(drvmap); }
	};

	struct DriverMapConeCellIterator : public std::iterator<std::input_iterator_tag, const RTLIL::Cell *> {
		DriverMap *drvmap;
		const RTLIL::SigBit *sig;

		DriverMapConeWireIterator sig_iter;

		DriverMapConeCellIterator(DriverMap *drvmap) : DriverMapConeCellIterator(drvmap, NULL) {}

		DriverMapConeCellIterator(DriverMap *drvmap, const RTLIL::SigBit *sig) : drvmap(drvmap), sig(sig), sig_iter(drvmap, sig)
		{
			if ((sig != NULL) && (!drvmap->count(*sig_iter))) {
				++(*this);
			}
		}

		inline RTLIL::Cell *operator*() const
		{
			std::pair<RTLIL::Cell *, std::set<RTLIL::SigBit>> &drv = drvmap->at(*sig_iter);
			return drv.first;
		};
		inline bool operator!=(const DriverMapConeCellIterator &other) const { return sig_iter != other.sig_iter; }
		inline bool operator==(const DriverMapConeCellIterator &other) const { return sig_iter == other.sig_iter; }
		inline void operator++()
		{
			do {
				++sig_iter;
				if (sig_iter.sig == NULL) {
					return;
				}
			} while (!drvmap->count(*sig_iter));
		}
	};

	struct DriverMapConeCellIterable {
		DriverMap *drvmap;
		const RTLIL::SigBit *sig;

		DriverMapConeCellIterable(DriverMap *drvmap, const RTLIL::SigBit *sig) : drvmap(drvmap), sig(sig) {}

		inline DriverMapConeCellIterator begin() { return DriverMapConeCellIterator(drvmap, sig); }
		inline DriverMapConeCellIterator end() { return DriverMapConeCellIterator(drvmap); }
	};

	struct DriverMapConeInputsIterator : public std::iterator<std::input_iterator_tag, const RTLIL::Cell *> {
		DriverMap *drvmap;
		const RTLIL::SigBit *sig;

		DriverMapConeWireIterator sig_iter;

		DriverMapConeInputsIterator(DriverMap *drvmap) : DriverMapConeInputsIterator(drvmap, NULL) {}

		DriverMapConeInputsIterator(DriverMap *drvmap, const RTLIL::SigBit *sig) : drvmap(drvmap), sig(sig), sig_iter(drvmap, sig)
		{
			if ((sig != NULL) && (drvmap->count(*sig_iter))) {
				++(*this);
			}
		}

		inline const RTLIL::SigBit& operator*() const
		{
			return *sig_iter;
		};
		inline bool operator!=(const DriverMapConeInputsIterator &other) const { return sig_iter != other.sig_iter; }
		inline bool operator==(const DriverMapConeInputsIterator &other) const { return sig_iter == other.sig_iter; }
		inline void operator++()
		{
			do {
				++sig_iter;
				if (sig_iter.sig == NULL) {
					return;
				}
			} while (drvmap->count(*sig_iter));
		}
	};

	struct DriverMapConeInputsIterable {
		DriverMap *drvmap;
		const RTLIL::SigBit *sig;

		DriverMapConeInputsIterable(DriverMap *drvmap, const RTLIL::SigBit *sig) : drvmap(drvmap), sig(sig) {}

		inline DriverMapConeInputsIterator begin() { return DriverMapConeInputsIterator(drvmap, sig); }
		inline DriverMapConeInputsIterator end() { return DriverMapConeInputsIterator(drvmap); }
	};

	DriverMap(RTLIL::Module *module) : module(module), sigmap(module)
	{
		CellTypes ct;
		ct.setup_internals();
		ct.setup_stdcells();

		for (auto &it : module->cells_) {
			if (ct.cell_known(it.second->type)) {
				std::set<RTLIL::SigBit> inputs, outputs;
				for (auto &port : it.second->connections()) {
					std::vector<RTLIL::SigBit> bits = sigmap(port.second).to_sigbit_vector();
					if (ct.cell_output(it.second->type, port.first))
						outputs.insert(bits.begin(), bits.end());
					else
						inputs.insert(bits.begin(), bits.end());
				}
				std::pair<RTLIL::Cell *, std::set<RTLIL::SigBit>> drv(it.second, inputs);
				for (auto &bit : outputs)
					(*this)[bit] = drv;
			}
		}
	}

	DriverMapConeWireIterable cone(const RTLIL::SigBit &sig) { return DriverMapConeWireIterable(this, &sig); }
	DriverMapConeInputsIterable cone_inputs(const RTLIL::SigBit &sig) { return DriverMapConeInputsIterable(this, &sig); }
	DriverMapConeCellIterable cell_cone(const RTLIL::SigBit &sig) { return DriverMapConeCellIterable(this, &sig); }
};

YOSYS_NAMESPACE_END

#endif
