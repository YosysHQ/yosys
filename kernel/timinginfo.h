/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
 *            (C) 2020  Eddie Hung    <eddie@fpgeh.com>
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

#ifndef TIMINGINFO_H
#define TIMINGINFO_H

#include "kernel/yosys.h"

YOSYS_NAMESPACE_BEGIN

struct TimingInfo
{
	struct NameBit
	{
		RTLIL::IdString name;
		int offset;
		NameBit() : offset(0) {}
		NameBit(const RTLIL::IdString name, int offset) : name(name), offset(offset) {}
		explicit NameBit(const RTLIL::SigBit &b) : name(b.wire->name), offset(b.offset) {}
		bool operator==(const NameBit& nb) const { return nb.name == name && nb.offset == offset; }
		bool operator!=(const NameBit& nb) const { return !operator==(nb); }
		unsigned int hash() const { return mkhash_add(name.hash(), offset); }
	};
	struct BitBit
	{
		NameBit first, second;
		BitBit(const NameBit &first, const NameBit &second) : first(first), second(second) {}
		BitBit(const SigBit &first, const SigBit &second) : first(first), second(second) {}
		bool operator==(const BitBit& bb) const { return bb.first == first && bb.second == second; }
		unsigned int hash() const { return mkhash_add(first.hash(), second.hash()); }
	};

	struct ModuleTiming
	{
		RTLIL::IdString type;
		dict<BitBit, int> comb;
		dict<NameBit, int> arrival, required;
	};

	dict<RTLIL::IdString, ModuleTiming> data;

	TimingInfo()
	{
	}

	TimingInfo(RTLIL::Design *design)
	{
		setup(design);
	}

	void setup(RTLIL::Design *design)
	{
		for (auto module : design->modules()) {
			if (!module->get_blackbox_attribute())
				continue;
			setup_module(module);
		}
	}

	const ModuleTiming& setup_module(RTLIL::Module *module)
	{
		auto r = data.insert(module->name);
		log_assert(r.second);
		auto &t = r.first->second;

		for (auto cell : module->cells()) {
			if (cell->type == ID($specify2)) {
				auto src = cell->getPort(ID(SRC));
				auto dst = cell->getPort(ID(DST));
				for (const auto &c : src.chunks())
					if (!c.wire->port_input)
						log_error("Module '%s' contains specify cell '%s' where SRC '%s' is not a module input.\n", log_id(module), log_id(cell), log_signal(src));
				for (const auto &c : dst.chunks())
					if (!c.wire->port_output)
						log_error("Module '%s' contains specify cell '%s' where DST '%s' is not a module output.\n", log_id(module), log_id(cell), log_signal(dst));
				int rise_max = cell->getParam(ID(T_RISE_MAX)).as_int();
				int fall_max = cell->getParam(ID(T_FALL_MAX)).as_int();
				int max = std::max(rise_max,fall_max);
				if (max < 0)
					log_error("Module '%s' contains specify cell '%s' with T_{RISE,FALL}_MAX < 0.\n", log_id(module), log_id(cell));
				if (cell->getParam(ID(FULL)).as_bool()) {
					for (const auto &s : src)
						for (const auto &d : dst) {
							auto r = t.comb.insert(BitBit(s,d));
							if (!r.second)
								log_error("Module '%s' contains multiple specify cells for SRC '%s' and DST '%s'.\n", log_id(module), log_signal(s), log_signal(d));
							r.first->second = max;
						}
				}
				else {
					log_assert(GetSize(src) == GetSize(dst));
					for (auto i = 0; i < GetSize(src); i++) {
						const auto &s = src[i];
						const auto &d = dst[i];
						auto r = t.comb.insert(BitBit(s,d));
						if (!r.second)
							log_error("Module '%s' contains multiple specify cells for SRC '%s' and DST '%s'.\n", log_id(module), log_signal(s), log_signal(d));
						r.first->second = max;
					}
				}
			}
			else if (cell->type == ID($specify3)) {
				auto src = cell->getPort(ID(SRC));
				auto dst = cell->getPort(ID(DST));
				for (const auto &c : src.chunks())
					if (!c.wire->port_input)
						log_error("Module '%s' contains specify cell '%s' where SRC '%s' is not a module input.\n", log_id(module), log_id(cell), log_signal(src));
				for (const auto &c : dst.chunks())
					if (!c.wire->port_output)
						log_error("Module '%s' contains specify cell '%s' where DST '%s' is not a module output.\n", log_id(module), log_id(cell), log_signal(dst));
				int rise_max = cell->getParam(ID(T_RISE_MAX)).as_int();
				int fall_max = cell->getParam(ID(T_FALL_MAX)).as_int();
				int max = std::max(rise_max,fall_max);
				if (max < 0)
					log_warning("Module '%s' contains specify cell '%s' with T_{RISE,FALL}_MAX < 0 which is currently unsupported. Ignoring.\n", log_id(module), log_id(cell));
				if (max <= 0) {
					log_debug("Module '%s' contains specify cell '%s' with T_{RISE,FALL}_MAX <= 0 which is currently unsupported. Ignoring.\n", log_id(module), log_id(cell));
					continue;
				}
				for (const auto &d : dst) {
					auto &v = t.arrival[NameBit(d)];
					v = std::max(v, max);
				}
			}
			else if (cell->type == ID($specrule)) {
				auto type = cell->getParam(ID(TYPE)).decode_string();
				if (type != "$setup" && type != "$setuphold")
					continue;
				auto src = cell->getPort(ID(SRC));
				auto dst = cell->getPort(ID(DST));
				for (const auto &c : src.chunks())
					if (!c.wire->port_input)
						log_error("Module '%s' contains specify cell '%s' where SRC '%s' is not a module input.\n", log_id(module), log_id(cell), log_signal(src));
				for (const auto &c : dst.chunks())
					if (!c.wire->port_input)
						log_error("Module '%s' contains specify cell '%s' where DST '%s' is not a module input.\n", log_id(module), log_id(cell), log_signal(dst));
				int max = cell->getParam(ID(T_LIMIT_MAX)).as_int();
				if (max < 0)
					log_warning("Module '%s' contains specify cell '%s' with T_LIMIT_MAX < 0 which is currently unsupported. Ignoring.\n", log_id(module), log_id(cell));
				if (max <= 0) {
					log_debug("Module '%s' contains specify cell '%s' with T_LIMIT_MAX <= 0 which is currently unsupported. Ignoring.\n", log_id(module), log_id(cell));
					continue;
				}
				for (const auto &s : src) {
					auto &v = t.required[NameBit(s)];
					v = std::max(v, max);
				}
			}
		}

		return t;
	}

	decltype(data)::const_iterator find(RTLIL::IdString module_name) const { return data.find(module_name); }
	decltype(data)::const_iterator end() const { return data.end(); }
	int count(RTLIL::IdString module_name) const { return data.count(module_name); }
	const ModuleTiming& at(RTLIL::IdString module_name) const { return data.at(module_name); }
};

YOSYS_NAMESPACE_END

#endif
