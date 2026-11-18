#ifndef NEWCELLTYPES_H
#define NEWCELLTYPES_H

#include "kernel/rtlil.h"
#include "kernel/yosys.h"

YOSYS_NAMESPACE_BEGIN

/**
 * This API is unstable.
 * It may change or be removed in future versions and break dependent code.
 */

namespace StaticCellTypes {

// Given by last internal cell type IdString constids.inc, compilation error if too low
constexpr int MAX_CELLS = 300;
// Currently given by _MUX16_, compilation error if too low
constexpr int MAX_PORTS = 20;
struct CellTableBuilder {
	struct PortList {
		std::array<RTLIL::IdString, MAX_PORTS> ports{};
		size_t count = 0;
		constexpr PortList() = default;
		constexpr PortList(std::initializer_list<RTLIL::IdString> init) {
			for (auto p : init) {
				ports[count++] = p;
			}
		}
		constexpr auto begin() const { return ports.begin(); }
		constexpr auto end() const { return ports.begin() + count; }
		constexpr bool contains(RTLIL::IdString port) const {
			for (size_t i = 0; i < count; i++) {
				if (port == ports[i])
					return true;
			}

			return false;
		}
		constexpr size_t size() const { return count; }
	};
	struct Features {
		bool is_evaluable = false;
		bool is_combinatorial = false;
		bool is_synthesizable = false;
		bool is_stdcell = false;
		bool is_ff = false;
		bool is_mem_noff = false;
		bool is_anyinit = false;
		bool is_tristate = false;
		bool has_side_effect = false;
		bool is_nondeterministic = false;
	};
	struct CellInfo {
		RTLIL::IdString type;
		PortList inputs, outputs;
		Features features;
	};
	std::array<CellInfo, MAX_CELLS> cells{};
	size_t count = 0;

	constexpr void setup_type(RTLIL::IdString type, std::initializer_list<RTLIL::IdString> inputs, std::initializer_list<RTLIL::IdString> outputs, const Features& features) {
		cells[count++] = {type, PortList(inputs), PortList(outputs), features};
	}
	constexpr void setup_internals_other();
	constexpr void setup_internals_eval();
	constexpr void setup_internals_ff();
	constexpr void setup_internals_anyinit();
	constexpr void setup_internals_mem_noff();
	constexpr void setup_stdcells_tristate();

	constexpr void setup_stdcells_eval();

	constexpr void setup_stdcells_ff();
	constexpr CellTableBuilder();

};

extern const CellTableBuilder builder;

struct PortInfo {
	struct PortLists {
		std::array<CellTableBuilder::PortList, MAX_CELLS> data{};
		constexpr CellTableBuilder::PortList operator()(IdString type) const {
			return data[type.raw()];
		}
		constexpr CellTableBuilder::PortList& operator[](size_t idx) {
			return data[idx];
		}
		constexpr size_t size() const { return data.size(); }
	};
	PortLists inputs {};
	PortLists outputs {};
	constexpr PortInfo();
};

struct Categories {
	struct Category {
		std::array<bool, MAX_CELLS> data{};
		constexpr bool operator()(IdString type) const {
			size_t idx = type.raw();
			if (idx >= MAX_CELLS)
				return false;
			return data[idx];
		}
		constexpr bool operator[](size_t idx) {
			return data[idx];
		}
		constexpr void set_id(IdString type, bool val = true) {
			size_t idx = type.raw();
			if (idx >= MAX_CELLS) {
				if (std::is_constant_evaluated())
					throw "cell type index out of range";
				log_abort();
			}
			data[idx] = val;
		}
		constexpr void set(size_t idx, bool val = true) {
			data[idx] = val;
		}
		constexpr size_t size() const { return data.size(); }
	};
	Category empty {};
	Category is_known {};
	Category is_evaluable {};
	Category is_combinatorial {};
	Category is_synthesizable {};
	Category is_stdcell {};
	Category is_ff {};
	Category is_mem_noff {};
	Category is_anyinit {};
	Category is_tristate {};
	Category has_side_effect {};
	Category is_nondeterministic {};
	constexpr Categories();
	constexpr static Category join(Category left, Category right) {
		Category c {};
		for (size_t i = 0; i < MAX_CELLS; ++i) {
			c.set(i, left[i] || right[i]);
		}
		return c;
	}
	constexpr static Category meet(Category left, Category right) {
		Category c {};
		for (size_t i = 0; i < MAX_CELLS; ++i) {
			c.set(i, left[i] && right[i]);
		}
		return c;
	}
	// Sketchy! Make sure to always meet with only the known universe.
	// In other words, no modus tollens allowed
	constexpr static Category complement(Category arg) {
		Category c {};
		for (size_t i = 0; i < MAX_CELLS; ++i) {
			c.set(i, !arg[i]);
		}
		return c;
	}
};

// Pure
extern const PortInfo port_info;
extern const Categories categories;

// Legacy
namespace Compat {
	extern const Categories::Category internals_all;
	extern const Categories::Category mem_ff;
	// old setup_internals + setup_stdcells
	extern const Categories::Category nomem_noff;
	extern const Categories::Category internals_mem_ff;
	// old setup_internals
	extern const Categories::Category internals_nomem_noff;
	// old setup_stdcells
	extern const Categories::Category stdcells_nomem_noff;
	extern const Categories::Category stdcells_mem;
	// old setup_internals_eval
	// static constexpr auto internals_eval = Categories::meet(internals_all, categories.is_evaluable);
};


};

struct NewCellType {
	RTLIL::IdString type;
	pool<RTLIL::IdString> inputs, outputs;
	bool is_evaluable;
	bool is_combinatorial;
	bool is_synthesizable;
};

struct NewCellTypes {
	StaticCellTypes::Categories::Category static_cell_types = StaticCellTypes::categories.empty;
	dict<IdString, NewCellType> custom_cell_types {};

	NewCellTypes() {
		static_cell_types = StaticCellTypes::categories.empty;
	}

	NewCellTypes(RTLIL::Design *design) {
		static_cell_types = StaticCellTypes::categories.empty;
		setup(design);
	}
	void setup(RTLIL::Design *design = NULL) {
		if (design)
			setup_design(design);
		static_cell_types = StaticCellTypes::categories.is_known;
	}
	void setup_design(RTLIL::Design *design) {
		for (auto module : design->modules())
			setup_module(module);
	}

	void setup_module(RTLIL::Module *module) {
		pool<IdString> inputs, outputs;
		for (auto wire_name : module->ports) {
			RTLIL::Wire *wire = module->wire(wire_name);
			if (wire->port_input)
				inputs.insert(wire->name);
			if (wire->port_output)
				outputs.insert(wire->name);
		}
		setup_type(module->name, inputs, outputs);
	}

	void setup_type(RTLIL::IdString type, const pool<RTLIL::IdString> &inputs, const pool<RTLIL::IdString> &outputs, bool is_evaluable = false, bool is_combinatorial = false, bool is_synthesizable = false) {
		NewCellType ct = {type, inputs, outputs, is_evaluable, is_combinatorial, is_synthesizable};
		custom_cell_types[ct.type] = ct;
	}

	void clear() {
		custom_cell_types.clear();
		static_cell_types = StaticCellTypes::categories.empty;
	}

	bool cell_known(IdString type) const {
		return static_cell_types(type) || custom_cell_types.count(type) != 0;
	}

	bool cell_output(IdString type, IdString port) const
	{
		if (static_cell_types(type) && StaticCellTypes::port_info.outputs(type).contains(port)) {
			return true;
		}
		auto it = custom_cell_types.find(type);
		return it != custom_cell_types.end() && it->second.outputs.count(port) != 0;
	}

	bool cell_input(IdString type, IdString port) const
	{
		if (static_cell_types(type) && StaticCellTypes::port_info.inputs(type).contains(port)) {
			return true;
		}
		auto it = custom_cell_types.find(type);
		return it != custom_cell_types.end() && it->second.inputs.count(port) != 0;
	}

	RTLIL::PortDir cell_port_dir(RTLIL::IdString type, RTLIL::IdString port) const
	{
		bool is_input, is_output;
		if (static_cell_types(type)) {
			is_input = StaticCellTypes::port_info.inputs(type).contains(port);
			is_output = StaticCellTypes::port_info.outputs(type).contains(port);
		} else {
			auto it = custom_cell_types.find(type);
			if (it == custom_cell_types.end())
				return RTLIL::PD_UNKNOWN;
			is_input = it->second.inputs.count(port);
			is_output = it->second.outputs.count(port);
		}
		return RTLIL::PortDir(is_input + is_output * 2);
	}
	bool cell_evaluable(IdString type) const
	{
		return static_cell_types(type) && StaticCellTypes::categories.is_evaluable(type);
	}
};

extern NewCellTypes yosys_celltypes;

YOSYS_NAMESPACE_END

#endif
