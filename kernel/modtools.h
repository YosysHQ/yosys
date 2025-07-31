/* -*- c++ -*-
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

#ifndef MODTOOLS_H
#define MODTOOLS_H

#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/celltypes.h"

YOSYS_NAMESPACE_BEGIN

struct ModIndex : public RTLIL::Monitor
{
	struct PortInfo {
		RTLIL::Cell* cell;
		RTLIL::IdString port;
		int offset;

		PortInfo() : cell(), port(), offset() { }
		PortInfo(RTLIL::Cell* _c, RTLIL::IdString _p, int _o) : cell(_c), port(_p), offset(_o) { }

		bool operator<(const PortInfo &other) const {
			if (cell != other.cell)
				return cell < other.cell;
			if (offset != other.offset)
				return offset < other.offset;
			return port < other.port;
		}

		bool operator==(const PortInfo &other) const {
			return cell == other.cell && port == other.port && offset == other.offset;
		}

		[[nodiscard]] Hasher hash_into(Hasher h) const {
			h.eat(cell->name);
			h.eat(port);
			h.eat(offset);
			return h;
		}
	};

	struct SigBitInfo
	{
		bool is_input, is_output;
		pool<PortInfo> ports;

		SigBitInfo() : is_input(false), is_output(false) { }

		bool operator==(const SigBitInfo &other) const {
			return is_input == other.is_input && is_output == other.is_output && ports == other.ports;
		}

		void merge(const SigBitInfo &other)
		{
			is_input = is_input || other.is_input;
			is_output = is_output || other.is_output;
			ports.insert(other.ports.begin(), other.ports.end());
		}
	};

	SigMap sigmap;
	RTLIL::Module *module;
	std::map<RTLIL::SigBit, SigBitInfo> database;
	int auto_reload_counter;
	bool auto_reload_module;

	void port_add(RTLIL::Cell *cell, RTLIL::IdString port, const RTLIL::SigSpec &sig)
	{
		for (int i = 0; i < GetSize(sig); i++) {
			RTLIL::SigBit bit = sigmap(sig[i]);
			if (bit.wire)
				database[bit].ports.insert(PortInfo(cell, port, i));
		}
	}

	void port_del(RTLIL::Cell *cell, RTLIL::IdString port, const RTLIL::SigSpec &sig)
	{
		for (int i = 0; i < GetSize(sig); i++) {
			RTLIL::SigBit bit = sigmap(sig[i]);
			if (bit.wire)
				database[bit].ports.erase(PortInfo(cell, port, i));
		}
	}

	const SigBitInfo &info(RTLIL::SigBit bit)
	{
		return database[sigmap(bit)];
	}

	void reload_module(bool reset_sigmap = true)
	{
		if (reset_sigmap) {
			sigmap.clear();
			sigmap.set(module);
		}

		database.clear();
		for (auto wire : module->wires())
			if (wire->port_input || wire->port_output)
				for (int i = 0; i < GetSize(wire); i++) {
					RTLIL::SigBit bit = sigmap(RTLIL::SigBit(wire, i));
					if (bit.wire && wire->port_input)
						database[bit].is_input = true;
					if (bit.wire && wire->port_output)
						database[bit].is_output = true;
				}
		for (auto cell : module->cells())
			for (auto &conn : cell->connections())
				port_add(cell, conn.first, conn.second);

		if (auto_reload_module) {
			if (++auto_reload_counter > 2)
				log_warning("Auto-reload in ModIndex -- possible performance bug!\n");
			auto_reload_module = false;
		}
	}

	void check()
	{
#ifndef NDEBUG
		if (auto_reload_module)
			return;

		for (auto it : database)
			log_assert(it.first == sigmap(it.first));

		auto database_bak = std::move(database);
		reload_module(false);

		if (!(database == database_bak))
		{
			for (auto &it : database_bak)
				if (!database.count(it.first))
					log("ModuleIndex::check(): Only in database_bak, not database: %s\n", log_signal(it.first));

			for (auto &it : database)
				if (!database_bak.count(it.first))
					log("ModuleIndex::check(): Only in database, not database_bak: %s\n", log_signal(it.first));
				else if (!(it.second == database_bak.at(it.first)))
					log("ModuleIndex::check(): Different content for database[%s].\n", log_signal(it.first));

			log_assert(database == database_bak);
		}
#endif
	}

	void notify_connect(RTLIL::Cell *cell, const RTLIL::IdString &port, const RTLIL::SigSpec &old_sig, const RTLIL::SigSpec &sig) override
	{
		log_assert(module == cell->module);

		if (auto_reload_module)
			return;

		port_del(cell, port, old_sig);
		port_add(cell, port, sig);
	}

	void notify_connect(RTLIL::Module *mod, const RTLIL::SigSig &sigsig) override
	{
		log_assert(module == mod);

		if (auto_reload_module)
			return;

		for (int i = 0; i < GetSize(sigsig.first); i++)
		{
			RTLIL::SigBit lhs = sigmap(sigsig.first[i]);
			RTLIL::SigBit rhs = sigmap(sigsig.second[i]);
			bool has_lhs = database.count(lhs) != 0;
			bool has_rhs = database.count(rhs) != 0;

			if (!has_lhs && !has_rhs) {
				sigmap.add(lhs, rhs);
			} else
			if (!has_rhs) {
				SigBitInfo new_info = database.at(lhs);
				database.erase(lhs);
				sigmap.add(lhs, rhs);
				lhs = sigmap(lhs);
				if (lhs.wire)
					database[lhs] = new_info;
			} else
			if (!has_lhs) {
				SigBitInfo new_info = database.at(rhs);
				database.erase(rhs);
				sigmap.add(lhs, rhs);
				rhs = sigmap(rhs);
				if (rhs.wire)
					database[rhs] = new_info;
			} else {
				SigBitInfo new_info = database.at(lhs);
				new_info.merge(database.at(rhs));
				database.erase(lhs);
				database.erase(rhs);
				sigmap.add(lhs, rhs);
				rhs = sigmap(rhs);
				if (rhs.wire)
					database[rhs] = new_info;
			}
		}
	}

	void notify_connect(RTLIL::Module *mod, const std::vector<RTLIL::SigSig>&) override
	{
		log_assert(module == mod);
		auto_reload_module = true;
	}

	void notify_blackout(RTLIL::Module *mod) override
	{
		log_assert(module == mod);
		auto_reload_module = true;
	}

	ModIndex(RTLIL::Module *_m) : sigmap(_m), module(_m)
	{
		auto_reload_counter = 0;
		auto_reload_module = true;
		module->monitors.insert(this);
	}

	~ModIndex()
	{
		module->monitors.erase(this);
	}

	SigBitInfo *query(RTLIL::SigBit bit)
	{
		if (auto_reload_module)
			reload_module();

		auto it = database.find(sigmap(bit));
		if (it == database.end())
			return nullptr;
		else
			return &it->second;
	}

	bool query_is_input(RTLIL::SigBit bit)
	{
		const SigBitInfo *info = query(bit);
		if (info == nullptr)
			return false;
		return info->is_input;
	}

	bool query_is_output(RTLIL::SigBit bit)
	{
		const SigBitInfo *info = query(bit);
		if (info == nullptr)
			return false;
		return info->is_output;
	}

	pool<PortInfo> &query_ports(RTLIL::SigBit bit)
	{
		static pool<PortInfo> empty_result_set;
		SigBitInfo *info = query(bit);
		if (info == nullptr)
			return empty_result_set;
		return info->ports;
	}

	void dump_db()
	{
		log("--- ModIndex Dump ---\n");

		if (auto_reload_module) {
			log("AUTO-RELOAD\n");
			reload_module();
		}

		for (auto &it : database) {
			log("BIT %s:\n", log_signal(it.first));
			if (it.second.is_input)
				log("  PRIMARY INPUT\n");
			if (it.second.is_output)
				log("  PRIMARY OUTPUT\n");
			for (auto &port : it.second.ports)
				log("  PORT: %s.%s[%d] (%s)\n", log_id(port.cell),
						log_id(port.port), port.offset, log_id(port.cell->type));
		}
	}
};

struct ModWalker
{
	struct PortBit
	{
		RTLIL::Cell *cell;
		RTLIL::IdString port;
		int offset;
		PortBit(Cell* c, IdString p, int o) : cell(c), port(p), offset(o) {}

		bool operator<(const PortBit &other) const {
			if (cell != other.cell)
				return cell < other.cell;
			if (port != other.port)
				return port < other.port;
			return offset < other.offset;
		}

		bool operator==(const PortBit &other) const {
			return cell == other.cell && port == other.port && offset == other.offset;
		}

		[[nodiscard]] Hasher hash_into(Hasher h) const {
			h.eat(cell->name);
			h.eat(port);
			h.eat(offset);
			return h;
		}
	};

	RTLIL::Design *design;
	RTLIL::Module *module;

	CellTypes ct;
	SigMap sigmap;

	dict<RTLIL::SigBit, pool<PortBit>> signal_drivers;
	dict<RTLIL::SigBit, pool<PortBit>> signal_consumers;
	pool<RTLIL::SigBit> signal_inputs, signal_outputs;

	dict<RTLIL::Cell*, pool<RTLIL::SigBit>> cell_outputs, cell_inputs;

	void add_wire(RTLIL::Wire *wire)
	{
		if (wire->port_input) {
			std::vector<RTLIL::SigBit> bits = sigmap(wire);
			for (auto bit : bits)
				if (bit.wire != NULL)
					signal_inputs.insert(bit);
		}

		if (wire->port_output) {
			std::vector<RTLIL::SigBit> bits = sigmap(wire);
			for (auto bit : bits)
				if (bit.wire != NULL)
					signal_outputs.insert(bit);
		}
	}

	void add_cell_port(RTLIL::Cell *cell, RTLIL::IdString port, std::vector<RTLIL::SigBit> bits, bool is_output, bool is_input)
	{
		for (int i = 0; i < int(bits.size()); i++)
			if (bits[i].wire != NULL) {
				PortBit pbit {cell, port, i};
				if (is_output) {
					signal_drivers[bits[i]].insert(pbit);
					cell_outputs[cell].insert(bits[i]);
				}
				if (is_input) {
					signal_consumers[bits[i]].insert(pbit);
					cell_inputs[cell].insert(bits[i]);
				}
			}
	}

	void add_cell(RTLIL::Cell *cell)
	{
		if (ct.cell_known(cell->type)) {
			for (auto &conn : cell->connections())
				add_cell_port(cell, conn.first, sigmap(conn.second),
						ct.cell_output(cell->type, conn.first),
						ct.cell_input(cell->type, conn.first));
		} else {
			for (auto &conn : cell->connections())
				add_cell_port(cell, conn.first, sigmap(conn.second), true, true);
		}
	}

	ModWalker(RTLIL::Design *design, RTLIL::Module *module = nullptr) : design(design), module(NULL)
	{
		ct.setup(design);
		if (module)
			setup(module);
	}

	void setup(RTLIL::Module *module, CellTypes *filter_ct = NULL)
	{
		this->module = module;

		sigmap.set(module);

		signal_drivers.clear();
		signal_consumers.clear();
		signal_inputs.clear();
		signal_outputs.clear();
		cell_inputs.clear();
		cell_outputs.clear();

		for (auto &it : module->wires_)
			add_wire(it.second);
		for (auto &it : module->cells_)
			if (filter_ct == NULL || filter_ct->cell_known(it.second->type))
				add_cell(it.second);
	}

	// get_* methods -- single RTLIL::SigBit

	inline bool get_drivers(pool<PortBit> &result, RTLIL::SigBit bit) const
	{
		bool found = false;
		if (signal_drivers.count(bit)) {
			const pool<PortBit> &r = signal_drivers.at(bit);
			result.insert(r.begin(), r.end());
			found = true;
		}
		return found;
	}

	inline bool get_consumers(pool<PortBit> &result, RTLIL::SigBit bit) const
	{
		bool found = false;
		if (signal_consumers.count(bit)) {
			const pool<PortBit> &r = signal_consumers.at(bit);
			result.insert(r.begin(), r.end());
			found = true;
		}
		return found;
	}

	inline bool get_inputs(pool<RTLIL::SigBit> &result, RTLIL::SigBit bit) const
	{
		bool found = false;
		if (signal_inputs.count(bit))
			result.insert(bit), found = true;
		return found;
	}

	inline bool get_outputs(pool<RTLIL::SigBit> &result, RTLIL::SigBit bit) const
	{
		bool found = false;
		if (signal_outputs.count(bit))
			result.insert(bit), found = true;
		return found;
	}

	// get_* methods -- container of RTLIL::SigBit's (always by reference)

	template<typename T>
	inline bool get_drivers(pool<PortBit> &result, const T &bits) const
	{
		bool found = false;
		for (RTLIL::SigBit bit : bits)
			if (signal_drivers.count(bit)) {
				const pool<PortBit> &r = signal_drivers.at(bit);
				result.insert(r.begin(), r.end());
				found = true;
			}
		return found;
	}

	template<typename T>
	inline bool get_consumers(pool<PortBit> &result, const T &bits) const
	{
		bool found = false;
		for (RTLIL::SigBit bit : bits)
			if (signal_consumers.count(bit)) {
				const pool<PortBit> &r = signal_consumers.at(bit);
				result.insert(r.begin(), r.end());
				found = true;
			}
		return found;
	}

	template<typename T>
	inline bool get_inputs(pool<RTLIL::SigBit> &result, const T &bits) const
	{
		bool found = false;
		for (RTLIL::SigBit bit : bits)
			if (signal_inputs.count(bit))
				result.insert(bit), found = true;
		return found;
	}

	template<typename T>
	inline bool get_outputs(pool<RTLIL::SigBit> &result, const T &bits) const
	{
		bool found = false;
		for (RTLIL::SigBit bit : bits)
			if (signal_outputs.count(bit))
				result.insert(bit), found = true;
		return found;
	}

	// get_* methods -- call by RTLIL::SigSpec (always by value)

	bool get_drivers(pool<PortBit> &result, RTLIL::SigSpec signal) const
	{
		std::vector<RTLIL::SigBit> bits = sigmap(signal);
		return get_drivers(result, bits);
	}

	bool get_consumers(pool<PortBit> &result, RTLIL::SigSpec signal) const
	{
		std::vector<RTLIL::SigBit> bits = sigmap(signal);
		return get_consumers(result, bits);
	}

	bool get_inputs(pool<RTLIL::SigBit> &result, RTLIL::SigSpec signal) const
	{
		std::vector<RTLIL::SigBit> bits = sigmap(signal);
		return get_inputs(result, bits);
	}

	bool get_outputs(pool<RTLIL::SigBit> &result, RTLIL::SigSpec signal) const
	{
		std::vector<RTLIL::SigBit> bits = sigmap(signal);
		return get_outputs(result, bits);
	}

	// has_* methods -- call by reference

	template<typename T>
	inline bool has_drivers(const T &sig) const {
		pool<PortBit> result;
		return get_drivers(result, sig);
	}

	template<typename T>
	inline bool has_consumers(const T &sig) const {
		pool<PortBit> result;
		return get_consumers(result, sig);
	}

	template<typename T>
	inline bool has_inputs(const T &sig) const {
		pool<RTLIL::SigBit> result;
		return get_inputs(result, sig);
	}

	template<typename T>
	inline bool has_outputs(const T &sig) const {
		pool<RTLIL::SigBit> result;
		return get_outputs(result, sig);
	}

	// has_* methods -- call by value

	inline bool has_drivers(RTLIL::SigSpec sig) const {
		pool<PortBit> result;
		return get_drivers(result, sig);
	}

	inline bool has_consumers(RTLIL::SigSpec sig) const {
		pool<PortBit> result;
		return get_consumers(result, sig);
	}

	inline bool has_inputs(RTLIL::SigSpec sig) const {
		pool<RTLIL::SigBit> result;
		return get_inputs(result, sig);
	}

	inline bool has_outputs(RTLIL::SigSpec sig) const {
		pool<RTLIL::SigBit> result;
		return get_outputs(result, sig);
	}
};

YOSYS_NAMESPACE_END

#endif
