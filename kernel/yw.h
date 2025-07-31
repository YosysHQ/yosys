/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2022  Jannis Harder <jix@yosyshq.com> <me@jix.one>
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

#ifndef YW_H
#define YW_H

#include "kernel/yosys.h"
#include "kernel/mem.h"

YOSYS_NAMESPACE_BEGIN

struct IdPath : public std::vector<RTLIL::IdString>
{
	template<typename... T>
	IdPath(T&&... args) : std::vector<RTLIL::IdString>(std::forward<T>(args)...) { }
	IdPath prefix() const { return {begin(), end() - !empty()}; }
	std::string str() const;

	bool has_address() const { int tmp; return get_address(tmp); };
	bool get_address(int &addr) const;

	[[nodiscard]] Hasher hash_into(Hasher h) const {
		h.eat(static_cast<const std::vector<RTLIL::IdString>&&>(*this));
		return h;
	}
};

struct WitnessHierarchyItem {
	RTLIL::Module *module;
	RTLIL::Wire *wire = nullptr;
	RTLIL::Cell *cell = nullptr;
	Mem *mem = nullptr;

	WitnessHierarchyItem(RTLIL::Module *module, RTLIL::Wire *wire) : module(module), wire(wire) {}
	WitnessHierarchyItem(RTLIL::Module *module, RTLIL::Cell *cell) : module(module), cell(cell) {}
	WitnessHierarchyItem(RTLIL::Module *module, Mem *mem) : module(module), mem(mem) {}
};

template<typename D, typename T>
void witness_hierarchy(RTLIL::Module *module, D data, T callback);

template<class T> static std::vector<std::string> witness_path(T *obj) {
	std::vector<std::string> path;
	if (obj->name.isPublic()) {
		auto hdlname = obj->get_string_attribute(ID::hdlname);
		for (auto token : split_tokens(hdlname))
			path.push_back("\\" + token);
	}
	if (path.empty())
		path.push_back(obj->name.str());
	return path;
}

struct ReadWitness
{
	struct Clock {
		IdPath path;
		int offset;
		bool is_posedge = false;
		bool is_negedge = false;
	};

	struct Signal {
		IdPath path;
		int offset;
		int width;
		bool init_only;

		int bits_offset;
	};

	struct Step {
		std::string bits;
	};

	std::string filename;
	std::vector<Clock> clocks;
	std::vector<Signal> signals;
	std::vector<Step> steps;

	ReadWitness(const std::string &filename);

	RTLIL::Const get_bits(int t, int bits_offset, int width) const;
};

template<typename D, typename T>
void witness_hierarchy_recursion(IdPath &path, int hdlname_mode, RTLIL::Module *module, D data, T &callback)
{
	auto const &const_path = path;
	size_t path_size = path.size();
	for (auto wire : module->wires())
	{
		auto hdlname = hdlname_mode < 0 ? std::vector<std::string>() : wire->get_hdlname_attribute();
		for (auto item : hdlname)
			path.push_back("\\" + item);
		if (hdlname.size() == 1 && path.back() == wire->name)
			hdlname.clear();
		if (!hdlname.empty())
			callback(const_path, WitnessHierarchyItem(module, wire), data);
		path.resize(path_size);
		if (hdlname.empty() || hdlname_mode <= 0) {
			path.push_back(wire->name);
			callback(const_path, WitnessHierarchyItem(module, wire), data);
			path.pop_back();
		}
	}

	for (auto cell : module->cells())
	{
		Module *child = module->design->module(cell->type);
		if (child == nullptr)
			continue;

		auto hdlname = hdlname_mode < 0 ? std::vector<std::string>() : cell->get_hdlname_attribute();
		for (auto item : hdlname)
			path.push_back("\\" + item);
		if (hdlname.size() == 1 && path.back() == cell->name)
			hdlname.clear();
		if (!hdlname.empty()) {
			D child_data = callback(const_path, WitnessHierarchyItem(module, cell), data);
			witness_hierarchy_recursion<D, T>(path, 1, child, child_data, callback);
		}
		path.resize(path_size);
		if (hdlname.empty() || hdlname_mode <= 0) {
			path.push_back(cell->name);
			D child_data = callback(const_path, WitnessHierarchyItem(module, cell), data);
			witness_hierarchy_recursion<D, T>(path, hdlname.empty() ? hdlname_mode : -1, child, child_data, callback);
			path.pop_back();
		}
	}

	for (auto mem : Mem::get_all_memories(module)) {
		std::vector<std::string> hdlname;

		if (hdlname_mode >= 0 && mem.cell != nullptr)
			hdlname = mem.cell->get_hdlname_attribute();
		for (auto item : hdlname)
			path.push_back("\\" + item);
		if (hdlname.size() == 1 && path.back() == mem.cell->name)
			hdlname.clear();
		if (!hdlname.empty()) {
			callback(const_path, WitnessHierarchyItem(module, &mem), data);
		}
		path.resize(path_size);

		if (hdlname.empty() || hdlname_mode <= 0) {
			path.push_back(mem.memid);
			callback(const_path, WitnessHierarchyItem(module, &mem), data);
			path.pop_back();

			if (mem.cell != nullptr && mem.cell->name != mem.memid) {
				path.push_back(mem.cell->name);
				callback(const_path, WitnessHierarchyItem(module, &mem), data);
				path.pop_back();
			}
		}
	}
}

template<typename D, typename T>
void witness_hierarchy(RTLIL::Module *module, D data, T callback)
{
	IdPath path;
	witness_hierarchy_recursion<D, T>(path, 0, module, data, callback);
}

YOSYS_NAMESPACE_END

#endif
