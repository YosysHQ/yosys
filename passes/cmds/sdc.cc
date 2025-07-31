#include "kernel/register.h"
#include "kernel/celltypes.h"
#include "kernel/rtlil.h"
#include "kernel/log.h"
#include <tcl.h>
#include <list>
#include <regex>
#include <optional>


USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN


struct SdcObjects {
	enum CollectMode {
		SimpleGetter,
		FullGetter,
		FullConstraint,
	} collect_mode;
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
		bool is_set(size_t idx) {
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
	using CellPin = std::pair<Cell*, IdString>;
	std::vector<std::string> design_ports;
	std::vector<std::pair<std::string, Cell*>> design_cells;
	std::vector<std::pair<std::string, CellPin>> design_pins;
	std::vector<std::pair<std::string, Wire*>> design_nets;

	dict<std::string, BitSelection> constrained_ports;
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
	SdcObjects(Design* design) {
		Module* top = design->top_module();
		if (!top)
			log_error("Top module couldn't be determined. Check 'top' attribute usage");
		for (auto port : top->ports) {
			design_ports.push_back(port.str().substr(1));
		}
		std::list<std::string> hierarchy{};
		sniff_module(hierarchy, top);
	}
	~SdcObjects() = default;
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
		for (auto [name, bits] : constrained_ports) {
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
};

template<typename T>
static bool parse_flag(char* arg, const char* flag_name, T& flag_var) {
	std::string expected = std::string("-") + flag_name;
	if (expected == arg) {
		flag_var = true;
		return true;
	}
	return false;
}

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

static std::pair<bool, SdcObjects::BitSelection> matches(std::string name, const std::string& pat, const MatchConfig& config) {
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
	SdcObjects::BitSelection bits = {};
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

static int sdc_get_pins_cmd(ClientData data, Tcl_Interp *interp, int objc, Tcl_Obj* const objv[])
{
	auto* objects = (SdcObjects*)data;
	// When this flag is present, the search for the pattern is made in all positions in the hierarchy.
	bool hierarchical_flag = false;
	bool regexp_flag = false;
	bool nocase_flag = false;
	std::string separator = "/";
	Tcl_Obj* of_objects = nullptr;
	std::vector<std::string> patterns;
	int i = 1;
	for (; i < objc; i++) {
		if (parse_flag(Tcl_GetString(objv[i]), "hierarchical", hierarchical_flag)) continue;
		if (parse_flag(Tcl_GetString(objv[i]), "hier", hierarchical_flag)) continue;
		if (parse_flag(Tcl_GetString(objv[i]), "regexp", regexp_flag)) continue;
		if (parse_flag(Tcl_GetString(objv[i]), "nocase", nocase_flag)) continue;
		if (!strcmp(Tcl_GetString(objv[i]), "-hsc")) {
			separator = Tcl_GetString(objv[++i]);
			continue;
		}
		if (!strcmp(Tcl_GetString(objv[i]), "-of_objects")) {
			of_objects = objv[++i];
			continue;
		}
		// Onto the next loop
		break;
	}
	for (; i < objc; i++) {
		patterns.push_back(Tcl_GetString(objv[i]));
	}
	if (objects->collect_mode == SdcObjects::CollectMode::SimpleGetter) {
		if (regexp_flag || hierarchical_flag || nocase_flag || separator != "/" || of_objects) {
			log_error("get_pins got unexpected flags in simple mode\n");
		}
		if (patterns.size() != 1) {
			log_error("get_pins got unexpected number of patterns in simple mode\n");
		}
	}

	MatchConfig config(regexp_flag, nocase_flag, hierarchical_flag);
	std::vector<std::tuple<std::string, SdcObjects::CellPin, SdcObjects::BitSelection>> resolved;
	for (auto pat : patterns) {
		bool found = false;
		for (auto [name, pin] : objects->design_pins) {
			auto [does_match, matching_bits] = matches(name, pat, config);
			if (does_match) {
				found = true;
				resolved.push_back(std::make_tuple(name, pin, matching_bits));
			}
		}
		if (!found)
			log_warning("No matches in design for pin %s\n", pat.c_str());
	}

	if (separator != "/") {
		Tcl_SetResult(interp, (char *)"Only '/' accepted as separator", TCL_STATIC);
		return TCL_ERROR;
	}

	Tcl_Obj *result = Tcl_NewListObj(resolved.size(), nullptr);
	for (auto [name, pin, matching_bits] : resolved) {
		// TODO change this to graph tracking if desired
		size_t width = (size_t)pin.first->getPort(pin.second).size();
		for (size_t i = 0; i < width; i++)
			if (matching_bits.is_set(i))
				Tcl_ListObjAppendElement(interp, result, Tcl_NewStringObj(name.c_str(), name.size()));

		if (objects->collect_mode != SdcObjects::CollectMode::FullConstraint)
			objects->constrained_pins[std::make_pair(name, pin)].merge(matching_bits);
	}

	Tcl_SetObjResult(interp, result);
	return TCL_OK;
}

static int sdc_get_ports_cmd(ClientData data, Tcl_Interp *interp, int objc, Tcl_Obj* const objv[])
{
	auto* objects = (SdcObjects*)data;
	bool regexp_flag = false;
	bool nocase_flag = false;
	std::vector<std::string> patterns;
	int i = 1;
	for (; i < objc; i++) {
		if (parse_flag(Tcl_GetString(objv[i]), "regexp", regexp_flag)) continue;
		if (parse_flag(Tcl_GetString(objv[i]), "nocase", nocase_flag)) continue;
		// Onto the next loop
		break;
	}
	for (; i < objc; i++) {
		patterns.push_back(Tcl_GetString(objv[i]));
	}
	if (objects->collect_mode == SdcObjects::CollectMode::SimpleGetter) {
		if (regexp_flag || nocase_flag) {
			log_error("get_ports got unexpected flags in simple mode\n");
		}
		if (patterns.size() != 1) {
			log_error("get_ports got unexpected number of patterns in simple mode\n");
		}
	}
	MatchConfig config(regexp_flag, nocase_flag, false);
	std::vector<std::tuple<std::string, SdcObjects::BitSelection>> resolved;
	for (auto pat : patterns) {
		bool found = false;
		for (auto name : objects->design_ports) {
			auto [does_match, matching_bits] = matches(name, pat, config);
			if (does_match) {
				found = true;
				resolved.push_back(std::make_tuple(name, matching_bits));
			}
		}
		if (!found)
			log_warning("No matches in design for port %s\n", pat.c_str());
	}
	Tcl_Obj *result = Tcl_NewListObj(resolved.size(), nullptr);
	for (auto [obj, matching_bits] : resolved) {
		Tcl_ListObjAppendElement(interp, result, Tcl_NewStringObj(obj.c_str(), obj.size()));
		if (objects->collect_mode != SdcObjects::CollectMode::FullConstraint) {
			if (objects->constrained_ports.count(obj) == 0) {
				objects->constrained_ports[obj] = matching_bits;
			} else {
				objects->constrained_ports[obj].merge(matching_bits);
			}
		}
	}

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

	std::string key_name         = Tcl_GetString(objv[1]);
	Tcl_Obj* key_value           = objv[2];
	std::string key_expect_type  = Tcl_GetString(objv[3]);
	std::string proc_name        = Tcl_GetString(objv[4]);

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
				// if (name + "/" + pin->name.str() == str) {
				// 	found = true;
				// 	objects->constrained_pins.insert(std::make_pair(name, pin));
				// 	break; // resolved, expected unique
				// }
			}
			if (!found)
				log_error("%s: pin %s not found\n", proc_name.c_str(), str);
		} else if (key_expect_type == "port") {
			bool found = false;
			for (auto name : objects->design_ports) {
				if (name == str) {
					found = true;
					objects->constrained_ports.insert(name);
					break; // resolved, expected unique
				}
			}
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
		Tcl_CreateObjCommand(interp, "get_pins", sdc_get_pins_cmd, (ClientData) objects.get(), NULL);
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
		// if (args.size() < 2)
		// 	log_cmd_error("Missing SDC file.\n");
		// TODO optional extra stub file
		size_t argidx;
		std::vector<std::string> opensta_stubs_paths;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-stubs" && argidx+1 < args.size()) {
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
		sdc.objects->dump();
		Tcl_Release(interp);
	}
} SdcPass;

YOSYS_NAMESPACE_END
