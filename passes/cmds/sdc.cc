#include "kernel/register.h"
#include "kernel/rtlil.h"
#include "kernel/log.h"
#include <tcl.h>
#include <list>
#include <optional>
#include <iostream>


USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct TclCall {
	Tcl_Interp *interp;
	int objc;
	Tcl_Obj* const* objv;
};

static int redirect_unknown(TclCall call);
static size_t get_node_count(Tcl_Interp* interp);

struct BitSelection {
	bool all = false;
	std::vector<bool> bits = {};
	void set_all() {
		bits.clear();
		all = true;
	}
	void clear() {
		bits.clear();
		all = false;
	}
	void set(size_t idx) {
		if (all)
			return;
		if (idx >= bits.size())
			bits.resize(idx + 1);
		bits[idx] = true;
	}
	void merge(const BitSelection& other) {
		if (all)
			return;
		if (other.all) {
			set_all();
			return;
		}
		if (other.bits.size() > bits.size())
			bits.resize(other.bits.size());
		for (size_t other_idx = 0; other_idx < other.bits.size(); other_idx++) {
			bool other_bit = other.bits[other_idx];
			if (other_bit)
				set(other_idx);
		}
	}
	void dump() {
		if (!all) {
			for (size_t i = 0; i < bits.size(); i++)
				if (bits[i])
					log("\t\t [%zu]\n", i);
		} else {
			log("\t\t FULL\n");
		}
	}
	bool is_set(size_t idx) const {
		if (all)
			return true;
		if (idx >= bits.size())
			return false;
		return bits[idx];
	}
	// TODO actually use this
	void compress(size_t size) {
		if (bits.size() < size)
			return;
		for (size_t i = 0; i < size; i++)
			if (!bits[i])
				return;
		bits.clear();
		bits.shrink_to_fit();
		all = true;
	}
};

struct SdcObjects {
	enum CollectMode {
		// getter-side object tracking with minimal features
		SimpleGetter,
		// getter-side object tracking with everything
		FullGetter,
		// constraint-side tracking
		FullConstraint,
	} collect_mode;
	enum ValueMode {
		// return something sensible and error on unknown
		Normal,
		// return a new graph node assuming unknown is overridden
		Graph,
	} value_mode;
	using CellPin = std::pair<Cell*, IdString>;
	Design* design;
	std::vector<std::pair<std::string, Wire*>> design_ports;
	std::vector<std::pair<std::string, Cell*>> design_cells;
	std::vector<std::pair<std::string, CellPin>> design_pins;
	std::vector<std::pair<std::string, Wire*>> design_nets;

	using PortPattern = std::tuple<std::string, Wire*, BitSelection>;
	using PinPattern = std::tuple<std::string, SdcObjects::CellPin, BitSelection>;
	std::vector<std::vector<PortPattern>> resolved_port_pattern_sets;
	std::vector<std::vector<PinPattern>> resolved_pin_pattern_sets;
	// TODO

	dict<std::pair<std::string, Wire*>, BitSelection> constrained_ports;
	pool<std::pair<std::string, Cell*>> constrained_cells;
	dict<std::pair<std::string, CellPin>, BitSelection> constrained_pins;
	dict<std::pair<std::string, Wire*>, BitSelection> constrained_nets;

	void sniff_module(std::list<std::string>& hierarchy, Module* mod) {
		std::string prefix;
		for (auto mod_name : hierarchy) {
			if (prefix.length())
				prefix += "/"; // TODO seperator?
			prefix += mod_name;
		}

		for (auto* wire : mod->wires()) {
			std::string name = wire->name.str();
			log_assert(name.length());
			// TODO: really skip internal wires?
			if (name[0] == '$')
				continue;
			name = name.substr(1);
			std::string path = prefix;
			if (path.length())
				path += "/";
			path += name;
			design_nets.push_back(std::make_pair(path, wire));
		}

		for (auto* cell : mod->cells()) {
			std::string name = cell->name.str();
			// TODO: really skip internal cells?
			if (name[0] == '$')
				continue;
			name = name.substr(1);
			std::string path = prefix;
			if (path.length())
				path += "/";
			path += name;
			design_cells.push_back(std::make_pair(path, cell));
			for (auto pin : cell->connections()) {
				IdString pin_name = pin.first;
				std::string pin_name_sdc = path + "/" + pin.first.str().substr(1);
				design_pins.push_back(std::make_pair(pin_name_sdc, std::make_pair(cell, pin_name)));
			}
			if (auto sub_mod = mod->design->module(cell->type)) {
				hierarchy.push_back(name);
				sniff_module(hierarchy, sub_mod);
				hierarchy.pop_back();
			}
		}
	}
	SdcObjects(Design* design) : design(design) {
		Module* top = design->top_module();
		if (!top)
			log_error("Top module couldn't be determined. Check 'top' attribute usage");
		for (auto port : top->ports) {
			design_ports.push_back(std::make_pair(port.str().substr(1), top->wire(port)));
		}
		std::list<std::string> hierarchy{};
		sniff_module(hierarchy, top);
	}
	~SdcObjects() = default;

	template <typename T, typename U>
	void build_normal_result(Tcl_Interp* interp, std::vector<std::tuple<std::string, T, BitSelection>>&& resolved, U& tgt, std::function<size_t(T&)> width, Tcl_Obj*& result) {
		if (!result)
			result = Tcl_NewListObj(resolved.size(), nullptr);
		for (auto [name, obj, matching_bits] : resolved) {
			for (size_t i = 0; i < width(obj); i++)
				if (matching_bits.is_set(i)) {
					Tcl_ListObjAppendElement(interp, result, Tcl_NewStringObj(name.c_str(), name.size()));
					break;
				}

		}
		size_t node_count = get_node_count(interp);
		tgt.emplace_back(std::move(resolved));
		log("%zu %zu\n", node_count, tgt.size());
		log_assert(node_count == tgt.size());
	}
	template <typename T>
	void merge_as_constrained(std::vector<std::tuple<std::string, T, BitSelection>>&& resolved) {
		for (auto [name, obj, matching_bits] : resolved) {
			merge_or_init(std::make_pair(name, obj), constrained_pins, matching_bits);
		}
	}
	void dump() {
		std::sort(design_ports.begin(), design_ports.end());
		std::sort(design_cells.begin(), design_cells.end());
		std::sort(design_pins.begin(), design_pins.end());
		std::sort(design_nets.begin(), design_nets.end());
		constrained_ports.sort();
		constrained_cells.sort();
		constrained_pins.sort();
		constrained_nets.sort();
		// log("Design ports:\n");
		// for (auto name : design_ports) {
		// 	log("\t%s\n", name.c_str());
		// }
		// log("Design cells:\n");
		// for (auto [name, cell] : design_cells) {
		// 	(void)cell;
		// 	log("\t%s\n", name.c_str());
		// }
		// log("Design pins:\n");
		// for (auto [name, pin] : design_pins) {
		// 	(void)pin;
		// 	log("\t%s\n", name.c_str());
		// }
		// log("Design nets:\n");
		// for (auto [name, net] : design_nets) {
		// 	(void)net;
		// 	log("\t%s\n", name.c_str());
		// }
		// log("\n");
		log("Constrained ports:\n");
		for (auto [ref, bits] : constrained_ports) {
			auto [name, port] = ref;
			(void)port;
			log("\t%s\n", name.c_str());
			bits.dump();
		}
		log("Constrained cells:\n");
		for (auto& [name, cell] : constrained_cells) {
			(void)cell;
			log("\t%s\n", name.c_str());
		}
		log("Constrained pins:\n");
		for (auto& [ref, bits] : constrained_pins) {
			auto [name, pin] = ref;
			(void)pin;
			log("\t%s\n", name.c_str());
			bits.dump();
		}
		log("Constrained nets:\n");
		for (auto& [ref, bits] : constrained_nets) {
			auto [name, net] = ref;
			(void)net;
			log("\t%s\n", name.c_str());
			bits.dump();
		}
		log("\n");
	}

	class KeepHierarchyWorker {
		std::unordered_set<Module*> tracked_modules = {};
		Design* design = nullptr;
		bool mark(Module* mod) {
			for (auto* cell : mod->cells()) {
				if (auto* submod = design->module(cell->type))
					if (mark(submod)) {
						mod->set_bool_attribute(ID::keep_hierarchy);
						return true;
					}
			}

			if (tracked_modules.count(mod)) {
				mod->set_bool_attribute(ID::keep_hierarchy);
				return true;
			}

			return false;
		}
	public:
		KeepHierarchyWorker(SdcObjects* objects, Design* d) : design(d) {
			for (auto [ref, _] : objects->constrained_ports) {
				tracked_modules.insert(ref.second->module);
			}
			for (auto& [_, cell] : objects->constrained_cells) {
				tracked_modules.insert(cell->module);
			}
			for (auto& [ref, _] : objects->constrained_pins) {
				tracked_modules.insert(ref.second.first->module);
			}
			for (auto& [ref, _] : objects->constrained_nets) {
				tracked_modules.insert(ref.second->module);
			}
			log_debug("keep_hierarchy tracked modules:\n");
			for (auto* mod : tracked_modules)
				log_debug("\t%s\n", mod->name);
		}
		bool mark() {
			return mark(design->top_module());
		}
	};
	void keep_hierarchy() {
		(void)KeepHierarchyWorker(this, design).mark();
	}
};

// TODO vectors
// TODO cell arrays?
struct MatchConfig {
	enum MatchMode {
		WILDCARD,
		REGEX,
	} match;
	bool match_case;
	enum HierMode {
		FLAT,
		TREE,
	} hier;
	MatchConfig(bool regexp_flag, bool nocase_flag, bool hierarchical_flag) :
		match(regexp_flag ? REGEX : WILDCARD),
		match_case(!nocase_flag),
		hier(hierarchical_flag ? FLAT : TREE) { }
};

static std::pair<bool, BitSelection> matches(std::string name, const std::string& pat, const MatchConfig& config) {
	(void)config;
	bool got_bit_index = false;;
	int bit_idx;
	std::string pat_base = pat;
	size_t pos = pat.rfind('[');
	if (pos != std::string::npos) {
		got_bit_index = true;
		pat_base = pat.substr(0, pos);
		std::string bit_selector = pat.substr(pos + 1, pat.rfind(']') - pos - 1);
		for (auto c : bit_selector)
			if (!std::isdigit(c))
				log_error("Unsupported bit selector %s in SDC pattern %s\n",
							bit_selector.c_str(), pat.c_str());
		bit_idx = std::stoi(bit_selector);

	}
	BitSelection bits = {};
	if (name == pat_base) {
		if (got_bit_index) {
			bits.set(bit_idx);
			return std::make_pair(true, bits);
		} else {
			bits.set_all();
			return std::make_pair(true, bits);

		}
	} else {
		return std::make_pair(false, bits);
	}
}

static int graph_node(TclCall call) {
	// TODO is that it?
	return redirect_unknown(call);
}

static int redirect_unknown(TclCall call) {
	// TODO redirect to different command
	Tcl_Obj *newCmd = Tcl_NewStringObj("unknown", -1);
	auto newObjc = call.objc + 1;
	Tcl_Obj **newObjv = new Tcl_Obj*[newObjc];
	newObjv[0] = newCmd;
	for (int i = 1; i < newObjc; i++) {
		newObjv[i] = call.objv[i - 1];
	}
	int result = Tcl_EvalObjv(call.interp, newObjc, newObjv, 0);
	Tcl_DecrRefCount(newCmd);
	delete[] newObjv;
	return result;
}


struct SdcGraphNode {
	using Child = std::variant<SdcGraphNode*, std::string>;
	std::vector<Child> children;
	SdcGraphNode() = default;
	void addChild(SdcGraphNode* child) {
		children.push_back(child);
	}
	void addChild(std::string tcl_string) {
		children.push_back(tcl_string);
	}
	void dump(std::ostream& os) const {
		bool first = true;
		for (auto child : children) {
			if (first) {
				first = false;
			} else {
				os << " ";
			}
			if (auto* s = std::get_if<std::string>(&child))
				os << *s;
			else if (SdcGraphNode*& c = *std::get_if<SdcGraphNode*>(&child)) {
				os << "[";
				c->dump(os);
				os << "]";
			} else {
				log_assert(false);
			}
		}
	}
};

static size_t get_node_count(Tcl_Interp* interp) {
	const char* idx_raw = Tcl_GetVar(interp, "sdc_call_index", TCL_GLOBAL_ONLY);
	log_assert(idx_raw);
	std::string idx(idx_raw);
	for (auto c : idx)
		if (!std::isdigit(c))
			log_error("sdc_call_index non-numeric value %s\n", idx.c_str());
	return std::stoi(idx);
}

std::vector<std::vector<std::string>> gather_nested_calls(Tcl_Interp* interp) {

	Tcl_Obj* listObj = Tcl_GetVar2Ex(interp, "sdc_calls", nullptr, TCL_GLOBAL_ONLY);
	int listLength;

	std::vector<std::vector<std::string>> sdc_calls;
	if (Tcl_ListObjLength(interp, listObj, &listLength) == TCL_OK) {
		for (int i = 0; i < listLength; i++) {
			Tcl_Obj* subListObj;
			std::vector<std::string> subList;
			if (Tcl_ListObjIndex(interp, listObj, i, &subListObj) != TCL_OK) {
				log_error("broken list of lists\n");
			}
			int subListLength;
			if (Tcl_ListObjLength(interp, subListObj, &subListLength) == TCL_OK) {
				// Valid list - extract elements
				for (int j = 0; j < subListLength; j++) {
					Tcl_Obj* elementObj;
					if (Tcl_ListObjIndex(interp, subListObj, j, &elementObj) == TCL_OK) {
						const char* elementStr = Tcl_GetString(elementObj);
						subList.push_back(std::string(elementStr));
					}
				}
			} else {
				// Single element, not a list
				const char* elementStr = Tcl_GetString(subListObj);
				subList.push_back(std::string(elementStr));
			}
			sdc_calls.push_back(subList);
		}
	}
	log_assert(sdc_calls.size() == get_node_count(interp));
	return sdc_calls;
}

std::vector<SdcGraphNode> build_graph(const std::vector<std::vector<std::string>>& sdc_calls) {
	size_t node_count = sdc_calls.size();
	std::vector<SdcGraphNode> graph(node_count);
	for (size_t i = 0; i < node_count; i++) {
		auto& new_node = graph[i];
		for (size_t j = 0; j < sdc_calls[i].size(); j++) {
			auto arg = sdc_calls[i][j];
			const std::string prefix = "YOSYS_SDC_MAGIC_NODE_";
			auto pos = arg.find(prefix);
			if (pos != std::string::npos) {
				std::string rest = arg.substr(pos + prefix.length());
				for (auto c : rest)
					if (!std::isdigit(c))
						log_error("weird thing %s in %s\n", rest.c_str(), arg.c_str());
				size_t arg_node_idx = std::stoi(rest);
				log_assert(arg_node_idx < graph.size());
				new_node.addChild(&graph[arg_node_idx]);
			} else {
				new_node.addChild(arg);
			}

		}
	}
	return graph;
}

std::vector<bool> node_ownership(const std::vector<SdcGraphNode>& graph) {
	std::vector<bool> has_parent(graph.size());
	for (auto node : graph) {
		for (auto child : node.children) {
			if (SdcGraphNode** pp = std::get_if<SdcGraphNode*>(&child)) {
				size_t idx = std::distance(&graph.front(), (const SdcGraphNode*)*pp);
				log_assert(idx < has_parent.size());
				has_parent[idx] = true;
			}
		}
	}
	return has_parent;
}

void dump_sdc_graph(const std::vector<SdcGraphNode>& graph, const std::vector<bool>& has_parent) {
	for (size_t i = 0; i < graph.size(); i++) {
		if (!has_parent[i]) {
			graph[i].dump(std::cout);
			std::cout << "\n";
		}
	}
}

void inspect_globals(Tcl_Interp* interp, bool dump_mode) {
	std::vector<std::vector<std::string>> sdc_calls = gather_nested_calls(interp);
	std::vector<SdcGraphNode> graph = build_graph(sdc_calls);
	if (dump_mode)
		dump_sdc_graph(graph, node_ownership(graph));
}

// patterns -> (pattern-object-bit)s
template <typename T, typename U>
std::vector<std::tuple<std::string, T, BitSelection>>
find_matching(U objects, const MatchConfig& config, const std::vector<std::string> &patterns, const char* obj_type)
{
	std::vector<std::tuple<std::string, T, BitSelection>> resolved;
	for (auto pat : patterns) {
		bool found = false;
		for (auto [name, obj] : objects) {
			auto [does_match, matching_bits] = matches(name, pat, config);
			if (does_match) {
				found = true;
				resolved.push_back(std::make_tuple(name, obj, matching_bits));
				// TODO add a continue statement, conditional on config
			}
		}
		if (!found)
			log_warning("No matches in design for %s %s\n", obj_type, pat.c_str());
	}
	return resolved;
}
struct GetterOpts {
	bool hierarchical_flag = false;
	bool regexp_flag = false;
	bool nocase_flag = false;
	std::string separator = "/";
	Tcl_Obj* of_objects = nullptr;
	std::vector<std::string> patterns = {};
	std::initializer_list<const char*> legals;
	const char* name;
	GetterOpts(const char* name, std::initializer_list<const char*> legals) : legals(legals), name(name) {}
	bool parse_opt(Tcl_Obj* obj, const char* opt_name) {
		char* arg = Tcl_GetString(obj);
		std::string expected = std::string("-") + opt_name;
		if (expected == arg) {
			if (!std::find_if(legals.begin(), legals.end(),
					   [&opt_name](const char* str) { return opt_name == str; }))
				log_cmd_error("Illegal argument %s for %s.\n", expected.c_str(), name);
			return true;
		}
		return false;
	}
	template<typename T>
	bool parse_flag(Tcl_Obj* obj, const char* flag_name, T& flag_var) {
		bool ret = parse_opt(obj, flag_name);
		if (ret)
			flag_var = true;
		return ret;
	}
	void parse(int objc, Tcl_Obj* const objv[]) {
		int i = 1;
		for (; i < objc; i++) {
			if (parse_flag(objv[i], "hierarchical", hierarchical_flag)) continue;
			if (parse_flag(objv[i], "hier", hierarchical_flag)) continue;
			if (parse_flag(objv[i], "regexp", regexp_flag)) continue;
			if (parse_flag(objv[i], "nocase", nocase_flag)) continue;
			if (parse_opt(objv[i], "hsc")) {
				log_assert(i + 1 < objc);
				separator = Tcl_GetString(objv[++i]);
				continue;
			}
			if (parse_opt(objv[i], "of_objects")) {
				log_assert(i + 1 < objc);
				of_objects = objv[++i];
				continue;
			}
			break;
		}
		for (; i < objc; i++) {
			patterns.push_back(Tcl_GetString(objv[i]));
		}
	};
	void check_simple() {
		if (regexp_flag || hierarchical_flag || nocase_flag || separator != "/" || of_objects) {
			log_error("%s got unexpected flags in simple mode\n", name);
		}
		if (patterns.size() != 1)
			log_error("%s got unexpected number of patterns in simple mode: %zu\n", name, patterns.size());
	}
	void check_simple_sep() {
		if (separator != "/")
			log_error("Only '/' accepted as separator");
	}
};

// void build_normal_result(Tcl_Interp* interp, size_t list_len, size_t width, const std::string& name, Tcl_Obj*& result, const BitSelection& matching_bits) {
// 	if (!result)
// 		result = Tcl_NewListObj(list_len, nullptr);
// 	for (size_t i = 0; i < width; i++)
// 		if (matching_bits.is_set(i))
// 			Tcl_ListObjAppendElement(interp, result, Tcl_NewStringObj(name.c_str(), name.size()));
// }

template <typename T>
void merge_or_init(const T& key, dict<T, BitSelection>& dst, const BitSelection& src) {
	if (dst.count(key) == 0) {
		dst[key] = src;
	} else {
		dst[key].merge(src);
	}
}

static int sdc_get_pins_cmd(ClientData data, Tcl_Interp *interp, int objc, Tcl_Obj* const objv[])
{
	auto* objects = (SdcObjects*)data;
	GetterOpts opts("get_pins", {"hierarchical", "hier", "regexp", "nocase", "hsc", "of_objects"});
	opts.parse(objc, objv);
	if (objects->collect_mode == SdcObjects::CollectMode::SimpleGetter)
		opts.check_simple();
	opts.check_simple_sep();

	MatchConfig config(opts.regexp_flag, opts.nocase_flag, opts.hierarchical_flag);
	std::vector<std::tuple<std::string, SdcObjects::CellPin, BitSelection>> resolved;
	const auto& pins = objects->design_pins;
	resolved = find_matching<SdcObjects::CellPin, decltype(pins)>(pins, config, opts.patterns, "pin");

	Tcl_Obj *result = nullptr;
	if (objects->value_mode == SdcObjects::ValueMode::Normal) {
		log_error("TODO normal\n");
		auto width = [](SdcObjects::CellPin& pin) -> size_t {
			return (size_t)pin.first->getPort(pin.second).size();
		};
		objects->build_normal_result<SdcObjects::CellPin, decltype(objects->resolved_pin_pattern_sets)>(interp, std::move(resolved), objects->resolved_pin_pattern_sets, width, result);
	} else if (objects->value_mode == SdcObjects::ValueMode::Graph)
		return graph_node(TclCall{interp, objc, objv});

	if (objects->collect_mode != SdcObjects::CollectMode::FullConstraint)
		objects->merge_as_constrained(std::move(resolved));
		// merge_or_init(std::make_pair(name, pin), objects->constrained_pins, matching_bits);
		// TODO
	// }

	
		// return objects->graph_node(interp, objc, objv, std::move(resolved), objects->resolved_pin_pattern_sets);

	if (result)
		Tcl_SetObjResult(interp, result);
	return TCL_OK;
}

static int sdc_get_ports_cmd(ClientData data, Tcl_Interp *interp, int objc, Tcl_Obj* const objv[])
{
	auto* objects = (SdcObjects*)data;
	GetterOpts opts("get_ports", {"regexp", "nocase"});
	opts.parse(objc, objv);
	if (objects->collect_mode == SdcObjects::CollectMode::SimpleGetter)
		opts.check_simple();

	MatchConfig config(opts.regexp_flag, opts.nocase_flag, false);
	std::vector<std::tuple<std::string, Wire*, BitSelection>> resolved;
	const auto& ports = objects->design_ports;
	resolved = find_matching<Wire*, decltype(ports)>(ports, config, opts.patterns, "port");

	Tcl_Obj *result = nullptr;
	for (auto [name, wire, matching_bits] : resolved) {
		if (objects->value_mode == SdcObjects::ValueMode::Normal)
			log_error("TODO normal\n");
			// objects->build_normal_result(interp, resolved.size(), wire->width, name, result, matching_bits);

		if (objects->collect_mode != SdcObjects::CollectMode::FullConstraint)
			merge_or_init(std::make_pair(name, wire), objects->constrained_ports, matching_bits);
	}

	if (objects->value_mode == SdcObjects::ValueMode::Graph) {
		return graph_node(TclCall{interp, objc, objv});
		// return objects->graph_node(interp, objc, objv, std::move(resolved), objects->resolved_port_pattern_sets);
	}
	if (result)
		Tcl_SetObjResult(interp, result);
	return TCL_OK;
}

static int sdc_get_nets_cmd(ClientData data, Tcl_Interp *interp, int objc, Tcl_Obj* const objv[])
{
	auto* objects = (SdcObjects*)data;
	GetterOpts opts("get_nets", {"hierarchical", "hier", "regexp", "nocase", "hsc", "of_objects"});
	opts.parse(objc, objv);
	if (objects->collect_mode == SdcObjects::CollectMode::SimpleGetter)
		opts.check_simple();

	MatchConfig config(opts.regexp_flag, opts.nocase_flag, false);
	std::vector<std::tuple<std::string, Wire*, BitSelection>> resolved;
	const auto& ports = objects->design_nets;
	resolved = find_matching<Wire*, decltype(ports)>(ports, config, opts.patterns, "net");

	Tcl_Obj *result = nullptr;
	for (auto [name, wire, matching_bits] : resolved) {
		if (objects->value_mode == SdcObjects::ValueMode::Normal)
			log_error("TODO normal\n");
			// objects->build_normal_result(interp, resolved.size(), wire->width, name, result, matching_bits);

		if (objects->collect_mode != SdcObjects::CollectMode::FullConstraint)
			merge_or_init(std::make_pair(name, wire), objects->constrained_nets, matching_bits);
	}

	if (objects->value_mode == SdcObjects::ValueMode::Graph) {
		return graph_node(TclCall{interp, objc, objv});
		// return objects->graph_node(interp, objc, objv, std::move(resolved), objects->resolved_port_pattern_sets);
	}
	if (result)
		Tcl_SetObjResult(interp, result);
	return TCL_OK;
}

std::optional<std::tuple<std::string, std::string>> split_at(std::string s)
{
	size_t pos = s.find('@');
	if (pos == std::string::npos)
		return std::nullopt;
	return std::make_tuple(s.substr(0, pos), s.substr(pos + 1));
}

// Whether string or list of strings, apply op to each string
void apply_args(Tcl_Interp *interp, std::function<void(const char*)> op, Tcl_Obj* obj)
{
	int length;
	Tcl_Obj **value_list;
	if (Tcl_ListObjGetElements(interp, obj, &length, &value_list) == TCL_OK) {
		for (int i = 0; i < length; i++) {
			op(Tcl_GetString(value_list[i]));
		}
	} else {
		op(Tcl_GetString(obj));
	}
}

static int ys_track_typed_key_cmd(ClientData data, Tcl_Interp *interp, int objc, Tcl_Obj* const objv[])
{
	log("ys_track_typed_key_cmd\n");
	auto* objects = (SdcObjects*)data;
	if (objc != 5)
		log_error("ys_track_typed_key: Unexpected number of arguments: %d (expected 5)\n", objc);

	if (objects->collect_mode != SdcObjects::CollectMode::FullConstraint)
		return TCL_OK;

	std::string key_name		 = Tcl_GetString(objv[1]);
	Tcl_Obj* key_value		   = objv[2];
	std::string key_expect_type  = Tcl_GetString(objv[3]);
	std::string proc_name		= Tcl_GetString(objv[4]);

	auto track_typed = [key_expect_type, objects, proc_name, key_name](const char* str) -> void {
		auto split = split_at(str);
		if (!split)
			log_error("%s: key %s should be a typed SDC object, but is something weird: %s\n",
				proc_name.c_str(), key_name.c_str(), str);

		if (key_expect_type == "pin") {
			log("PIN! %s\n", str);
			bool found = false;
			for (auto [name, pin] : objects->design_pins) {
				log_error("TODO temporarily disabled due to working on a different flow\n");
				// if (name + "/" + pin.name.str() == str) {
				// 	found = true;
				// 	objects->constrained_pins.insert(std::make_pair(name, pin));
				// 	break; // resolved, expected unique
				// }
			}
			if (!found)
				log_error("%s: pin %s not found\n", proc_name.c_str(), str);
		} else if (key_expect_type == "port") {
			bool found = false;
			log_error("TODO temporarily disabled due to working on a different flow\n");
			// for (auto [name, ] : objects->design_ports) {
			// 	if (name == str) {
			// 		found = true;
			// 		objects->constrained_ports.insert(name);
			// 		break; // resolved, expected unique
			// 	}
			// }
			if (!found)
				log_error("%s: port %s not found\n", proc_name.c_str(), str);
		} else {
			// TODO
			log_warning("%s: unsupported type %s\n", proc_name.c_str(), key_expect_type.c_str());
		}
	};
	apply_args(interp, track_typed, key_value);
	return TCL_OK;
}


class SDCInterpreter
{
private:
	Tcl_Interp* interp = nullptr;
public:
	std::unique_ptr<SdcObjects> objects;
	~SDCInterpreter() {
		if (interp)
			Tcl_DeleteInterp(interp);
	}
	static SDCInterpreter& get() {
		static SDCInterpreter instance;
		return instance;
	}
	Tcl_Interp* fresh_interp(Design* design) {
		if (interp)
			Tcl_DeleteInterp(interp);

		interp = Tcl_CreateInterp();
		if (Tcl_Init(interp)!=TCL_OK)
			log_error("Tcl_Init() call failed - %s\n",Tcl_ErrnoMsg(Tcl_GetErrno()));

		objects = std::make_unique<SdcObjects>(design);
		objects->collect_mode = SdcObjects::CollectMode::SimpleGetter;
		objects->value_mode = SdcObjects::ValueMode::Graph;
		Tcl_CreateObjCommand(interp, "get_pins", sdc_get_pins_cmd, (ClientData) objects.get(), NULL);
		Tcl_CreateObjCommand(interp, "get_nets", sdc_get_nets_cmd, (ClientData) objects.get(), NULL);
		Tcl_CreateObjCommand(interp, "get_ports", sdc_get_ports_cmd, (ClientData) objects.get(), NULL);
		Tcl_CreateObjCommand(interp, "ys_track_typed_key", ys_track_typed_key_cmd, (ClientData) objects.get(), NULL);
		return interp;
	}
};

// Also see TclPass
struct SdcPass : public Pass {
	// TODO help
	SdcPass() : Pass("sdc", "sniff at some SDC") { }
	void execute(std::vector<std::string> args, RTLIL::Design *design) override {
		log_header(design, "Executing SDC pass.\n");
		size_t argidx;
		bool graph_mode = false;
		bool dump_mode = false;
		bool keep_hierarchy_mode = false;
		std::vector<std::string> opensta_stubs_paths;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-graph") {
				graph_mode = true;
				continue;
			} else if (args[argidx] == "-dump") {
				dump_mode = true;
				continue;
			} else if (args[argidx] == "-keep_hierarchy") {
				keep_hierarchy_mode = true;
				continue;
			} else if (args[argidx] == "-stubs" && argidx+1 < args.size()) {
				opensta_stubs_paths.push_back(args[++argidx]);
				continue;
			}
			break;
		}
		if (argidx >= args.size())
			log_cmd_error("Missing SDC file.\n");

		std::string sdc_path = args[argidx];
		SDCInterpreter& sdc = SDCInterpreter::get();
		Tcl_Interp *interp = sdc.fresh_interp(design);
		Tcl_Preserve(interp);
		std::string stub_path = "+/sdc/stubs.sdc";
		rewrite_filename(stub_path);
		if (Tcl_EvalFile(interp, stub_path.c_str()) != TCL_OK)
			log_cmd_error("SDC interpreter returned an error in stub preamble file: %s\n", Tcl_GetStringResult(interp));
		for (auto path : opensta_stubs_paths)
			if (Tcl_EvalFile(interp, path.c_str()) != TCL_OK)
				log_cmd_error("SDC interpreter returned an error in OpenSTA stub file %s: %s\n", path.c_str(), Tcl_GetStringResult(interp));
		if (Tcl_EvalFile(interp, sdc_path.c_str()) != TCL_OK)
			log_cmd_error("SDC interpreter returned an error: %s\n", Tcl_GetStringResult(interp));
		if (dump_mode)
			sdc.objects->dump();
		if (keep_hierarchy_mode)
			sdc.objects->keep_hierarchy();
		inspect_globals(interp, graph_mode);
		Tcl_Release(interp);
	}
} SdcPass;

YOSYS_NAMESPACE_END
