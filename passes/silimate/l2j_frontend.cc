/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012 Silimate Inc
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
// SILIMATE: Custom frontend using liberty2json
#include "kernel/register.h"
#include "kernel/log.h"
#include "libs/json11/json11.hpp"

using namespace std::literals::string_literals;

YOSYS_NAMESPACE_BEGIN

using Json = json11:: Json;

// Helpers
/// @brief Gets an attribute as a reference to a Json::object, or if the key is
///        undefined, returns a default value. If the attribute exists but is
///        not an object, log_error is called, exiting the program
/// @param description A description of the container object to use in error messages
/// @param o The container object
/// @param key The key used to access the attribute in question
/// @param default_ The fallback default value
/// @return reference to either the array attribute if found or the default
///         otherwise
inline const Json::object &get_object_attr(std::string_view description, const Json::object &o, std::string key, const Json::object &default_) {
	const Json::object *result = &default_;
	auto it = o.find(key);
	if (it != o.end()) {
		if (it->second.type() == Json::Type::OBJECT) {
			result = &it->second.object_items();
		} else {
			log_error("%s attribute of %s is not a valid object\n", key, description);
		}
	}
	return *result;
}

/// @brief Gets an attribute as a reference to a Json::array, or if the key is
///        undefined, returns a default value. If the attribute exists but is
///        not an object, log_error is called, exiting the program
/// @param description A description of the container object to use in error messages
/// @param o The container object
/// @param key The key used to access the attribute in question
/// @param default_ The fallback default value
/// @return reference to either the array attribute if found or the default
///         otherwise
inline const Json::array &get_array_attr(std::string_view description, const Json::object &o, std::string key, const Json::array &default_) {
	const Json::array *result = &default_;
	auto it = o.find(key);
	if (it != o.end()) {
		if (it->second.type() == Json::Type::ARRAY) {
			result = &it->second.array_items();
		} else {
			log_error("%s attribute of %s is not a valid array\n", key, description);
		}
	}
	return *result;
}

/// @brief Gets an attribute as an string, or if the key is undefined,
///        returns a default value. If the attribute exists but is not a string
///        log_error is called, exiting the program
/// @param description A description of the container object to use in error messages
/// @param o The container object
/// @param key The key used to access the attribute in question
/// @param default_ The fallback default value
/// @return the string attribute if found or the default otherwise
inline std::string get_string_attr(std::string_view description, const Json::object &o, std::string key, std::string_view default_) {
	std::string result{default_};
	auto it = o.find(key);
	if (it != o.end()) {
		if (it->second.type() == Json::Type::STRING) {
			result = it->second.string_value();
		} else {
			log_error("%s attribute of %s is not a valid string\n", key, description);
		}
	}
	return result;
}

/// @brief Gets an attribute as an boolean, or if the key is undefined,
///        returns a default value. If the attribute exists but is not a
///        boolean, it emulates the behavior of the Python programming language
///        as to "truthiness."
/// @param description A description of the container object to use in error messages
/// @param o The container object
/// @param key The key used to access the attribute in question
/// @param default_ The fallback default value
/// @return the boolean attribute if found or the default otherwise
inline bool get_bool_attr(std::string_view description, const Json::object &o, std::string key, bool default_) {
	bool result = default_;
	auto it = o.find(key);
	if (it == o.end()) {
		return result;
	}
	switch (it->second.type()) {
	case Json::Type::BOOL:
		result = it->second.bool_value();
		break;
	case Json::Type::NUMBER:
		result = bool(it->second.number_value());
		break;
	case Json::Type::STRING:
		result = it->second.string_value().length() != 0;
		break;
	case Json::Type::ARRAY:
		result = it->second.array_items().size() != 0;
		break;
	case Json::Type::OBJECT:
		result = it->second.object_items().size() != 0;
		break;
	case Json::Type::NUL:
		result = false;
		break;
	}
	return result;
}

/// @brief Gets an attribute as a double-width floating point number, or if the
///        key is undefined, returns a default value. If the attribute exists
///        but is not a number; strings are attempted to be parsed first and
///        calls log_error to exit the program on failure. All other types cause
///        log_error to be called unconditionally
/// @param description A description of the container object to use in error messages
/// @param o The container object
/// @param key The key used to access the attribute in question
/// @param default_ The fallback default value
/// @return the numeric attribute if found or the default otherwise
inline double get_numeric_attr(std::string_view description, const Json::object &o, std::string key, double default_) {
	double result = default_;
	auto it = o.find(key);
	if (it != o.end()) {
		if (it->second.type() == Json::Type::STRING) {
			std::stringstream parse(it->second.string_value());
			parse >> result;
			if (parse.fail()) {
				log_error("%s attribute of %s is not a valid number\n", key, description);
			}
		} else if (it->second.type() == Json::Type::NUMBER) {
			result = it->second.number_value();
		} else {
			log_error("%s attribute of %s is not a valid number\n", key, description);
		}
	}
	return result;
}

/// @brief Iterates over the .groups attribute of JSON objects.
///        If the attribute doesn't exist, it iterates over nothing.
///        If the attribute exists but is not an array, log_error is called,
///        terminating the program
///        If any of the elements of the array are not objects, log_error is
///        also called, terminating the program
/// @param description A description of the container object to use in error messages
/// @param o The container object
/// @param executor The lambda to execute that takes a constant reference to the
///        JSON object representing the group.
inline void for_each_group(std::string_view description, const Json::object &o, std::function<void(const Json::object &)> executor) {
	Json::array empty_arr;
	const Json::array &groups = get_array_attr(description, o, "groups", empty_arr);
	for (const auto &group_j: groups) {
		if (group_j.type() != Json::Type::OBJECT) {
			log_error("Group in %s is not an object.\n", description);
		}
		auto group = group_j.object_items();
		executor(group);
	}
}

/// @brief Returns the first object of the .names array attribute of a given
///        string. If either the array or the name fail validation (i.e. they
///        exist but are not the correct type,) the program will call log_error
///        and terminate
/// @param description A description of the container to use in error messages
/// @param named_object The container in question
/// @return The first name if both the .names array attribute and the name itself
///         both exist, otherwise nullopt
inline std::optional<std::string> single_name_of(std::string_view description, const Json::object &named_object) {
	Json::array empty_arr;
	const Json::array &names = get_array_attr(description, named_object, "names", empty_arr);
	if (names.size()) {
		Json name_j = names[0];
		if (name_j.type() != Json::Type::STRING) {
			log_error("First entry in name array of %s is not a string\n", description);
		}
		return name_j.string_value();
	} else {
		return std::nullopt;
	}
}

// TypeWidth object (dynamic in the original Python)
struct TypeWidth {
	bool downto;
	int bit_from;
	int bit_to;
	int bit_width;

	/// @brief Constructs a TypeWidth declaration object from its JSON equivalent
	///        cell. May call log_error and terminate the program on typing errors
	/// @param description A description of the container to use in error messages
	/// @param type The type JSON object
	/// @return newly constructed type-width object
	static TypeWidth from_json_object(std::string_view description, const Json::object &type) {
		std::string type_group_desc = std::string(description) + " type group";
		bool downto = get_bool_attr(type_group_desc, type, "downto", false);
		int bit_from = get_numeric_attr(type_group_desc, type, "bit_from", 0);
		int bit_to = get_numeric_attr(type_group_desc, type, "bit_to", 0);
		int bit_width = get_numeric_attr(type_group_desc, type, "bit_width", (bit_from - bit_to) + 1);
		return TypeWidth { downto, bit_from, bit_to, bit_width};
	}

	/// @brief Collects and constructs TypeWidth objects from a container, be it
	///        either types declared in the top-level library or types local to a
	///        cell. May call log_error and terminate the program on typing errors
	/// @param description A description of the container to use in error messages
	/// @param container The JSON object containing types
	/// @return A mapping from the types' names to their newly constructed
	///         TypeWidth objects.
	static auto collect_types(std::string_view description, const Json::object &container) {
		dict<std::string, TypeWidth> result;
		for_each_group(description, container, [&](const Json::object &g){
			Json::object empty_obj;
			if (!g.count("type")) {
				return;
			}
			auto &type = get_object_attr(description, g, "type", empty_obj);
			auto type_group_desc = std::string(description) + " type group";
			auto type_name = single_name_of(type_group_desc, type);
			if (!type_name) {
				log_warning("Nameless type encountered\n");
				return;
			}
			result[*type_name] = TypeWidth::from_json_object(std::string(description) + " '" + *type_name + "'", type);
		});
		return result;
	}
};

/// @brief Convenience method to add a port to an RTLIL\:\:Module from liberty
///        information. Will terminate program by calling log_error iff
///        - Direction is not "internal", "input", "output", or "inout"
/// @param module_ The parent module
/// @param pin_name The name of the new port to add
/// @param width The width of the new port to add
/// @param direction A valid liberty file pin direction
/// @param upto If true, [from:to] else [to:from].
/// @param offset The start bit index. The end bit index is thus offset+width
/// @return A pointer to the newly created wire inside the RTLIL\:\:Module or
///         nullptr iff the port is internal OR the module already has a wire by
///         the same name (can happen with bus/bundle declarations.)
RTLIL::Wire *add_port(RTLIL::Module *module_, std::string_view pin_name, int width, std::string_view direction, bool upto=false, int offset=0) {
	if (direction == "internal") {
		log("Skipping internal port %s/%s.\n", module_->name.c_str(), pin_name);
		return nullptr;
	}
	IdString idstr("\\" + std::string(pin_name));
	if (module_->wire(idstr)) {
		log_warning("A pin with the name %s already exists in %s. The pin will be skipped.\n", idstr.c_str(), module_->name.c_str());
		return nullptr;
	}
	RTLIL::Wire *port = module_->addWire(idstr, width);
	port->upto = upto;
	port->start_offset = offset;
	if (direction.find("in") != std::string::npos) {
		port->port_input = true;
	}
	if (direction.find("out") != std::string::npos) {
		port->port_output = true;
	}
	if (!port->port_input && !port->port_output) {
		log_error("Pin %s/%s has an unknown direction.\n", module_->name.c_str(), pin_name);
	}
	module_->fixup_ports();
	return port;
}

// Frontend
struct L2JFrontend : public Frontend {
	L2JFrontend() : Frontend("liberty2json", "read from a liberty file translated into the silimate/liberty2json format") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    read_liberty2json [filename]\n");
		log("\n");
		log("    Read cells from files emitted from liberty2json as blackbox modules into");
		log("    current design.\n");
	}
	void execute(std::istream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design) override
	{
		extra_args(f, filename, args, 1);

		std::stringstream buffer;
		buffer << f->rdbuf();
		std::string err = "";
		auto top_j = Json::parse(buffer.str(), err);
		if (err.length()) {
			log_error("Failed to parse liberty2json file: %s\n", err);
		}

		Json::object empty_obj;
		Json::array empty_arr;

		if (top_j.type() == Json::Type::NUL) {
			log_warning("top-level entry is null. nothing to import.\n");
			return;
		}
		if (top_j.type() != Json::Type::OBJECT) {
			log_error("top-level entry is not an object\n");
		}

		auto top = top_j.object_items();
		if (top["library"].type() != Json::Type::OBJECT) {
			log_error("top-level library attribute is not an object\n");
		}
		auto library = top["library"].object_items();

		std::string leakage_power_unit = get_string_attr("top level library", library, "leakage_power_unit", "1pW");

		// Group processing, part 1: record global bus type widths
		TypeWidth default_type_width = TypeWidth {false, 0, 0, 1};
		dict<std::string, TypeWidth> type_widths = TypeWidth::collect_types("top-level library", library);

		// Group processing, part 2: create blackbox modules
		pool<IdString> already_defined;
		for_each_group("top-level library", library, [&](const Json::object &g) {
			if (!g.count("cell")) {
				return;
			}
			const Json::object &cell = get_object_attr("top-level group", g, "cell", empty_obj);
			auto cell_name = single_name_of("cell", cell);
			if (!cell_name) {
				log_warning("Nameless cell encountered\n");
				return;
			}

			IdString module_name { "\\"s + *cell_name };
			if (already_defined.count(module_name)) {
				log_warning("Library cell already defined: %s\n", cell_name->c_str());
				return;
			}
			already_defined.insert(module_name);

			std::string cell_desc = "cell " + *cell_name;

			dict<std::string, TypeWidth> local_type_widths = TypeWidth::collect_types(cell_desc, cell);

			// Memory and stdcell
			bool is_memory = false, is_stdcell = true;
			bool dont_touch = get_bool_attr(cell_desc, cell, "dont_touch", false);
			bool dont_use = get_bool_attr(cell_desc, cell, "dont_use", false);
			if (dont_touch || dont_use) {
				is_stdcell = false;
			}
			for_each_group(cell_desc, cell, [&](const Json::object &g) {
				if (g.count("memory")) {
					is_memory = true; is_stdcell = false;
				}
			});

			// PPA Numbers (TODO: add dynamic power data)
			double area = get_numeric_attr(cell_desc, cell, "area", 0.0);
			double cell_leakage_power = get_numeric_attr(cell_desc, cell, "cell_leakage_power", 0.0);

			log("  Creating liberty module %s\n", module_name.c_str());
			auto current_module = design->addModule(module_name);
			current_module->set_bool_attribute(ID(blackbox));
			if (is_memory) {
				current_module->set_bool_attribute(ID(memory));
			}
			if (is_stdcell) {
				current_module->set_bool_attribute(ID(stdcell));
			}
			current_module->set_string_attribute(ID(area), std::to_string(area));
			current_module->set_string_attribute(ID(LeakagePower), std::to_string(cell_leakage_power));
			current_module->set_string_attribute(ID(leakage_power_unit), leakage_power_unit);

			size_t group_idx = 0;
			size_t pin_idx = 0;
			size_t bus_idx = 0;
			size_t bundle_idx = 0;
			for_each_group(cell_desc, cell, [&](const Json::object &g) {
				std::stringstream group_desc;
				group_desc << cell_desc << " group " << group_idx++;
				if (g.count("pin")) {
					std::stringstream pin_desc;
					pin_desc << cell_desc << " pin " << pin_idx++;
					auto &pin = get_object_attr(group_desc.str(), g, "pin", empty_obj);
					std::string direction = get_string_attr(pin_desc.str(), pin, "direction", "input");
					auto &pin_names = get_array_attr(pin_desc.str(), pin, "names", empty_arr);
					for (auto &pin_name: pin_names) {
						if (!pin_name.is_string()) {
							log_error("One of the names of %s is not a string.\n", pin_desc.str());
						}
						add_port(current_module, pin_name.string_value(), 1, direction);
					}
				} else if (g.count("bus")) {
					std::stringstream bus_desc;
					bus_desc << cell_desc << " bus " << bus_idx++;
					auto &bus = get_object_attr(group_desc.str(), g, "bus", empty_obj);

					// Determine direction
					std::string direction = "";
					if (bus.count("direction")) {
						direction = get_string_attr(bus_desc.str(), bus, "direction", "input");
					} else {
						for_each_group(bus_desc.str(), bus, [&](const Json::object &sg) {
							if (!sg.count("pin")) {
								return;
							}
							auto pin = get_object_attr(bus_desc.str() + " subgroup", sg, "pin", empty_obj);
							if (!pin.count("direction")) {
								return;
							}
							direction = get_string_attr(bus_desc.str() + " pin", pin, "direction", "input");
						});
					}
					if (direction == "") {
						log_warning("No direction found for %s. Assuming input.\n", bus_desc.str());
						direction = "input";
					}

					auto bus_type = get_string_attr(bus_desc.str(), bus, "bus_type", "");
					TypeWidth *bus_type_width = nullptr;
					if (type_widths.count(bus_type)) {
						bus_type_width = &type_widths[bus_type];
					} else if (local_type_widths.count(bus_type)) {
						bus_type_width = &local_type_widths[bus_type];
					} else {
						// bus_type_width = &default_type_width; // <-- possible alternate route
						log_warning("No type '%s' found for bus %s - skipping\n", bus_type, bus_desc.str());
						return;
					}
					auto &bus_names = get_array_attr(bus_desc.str(), bus, "names", empty_arr);
					for (auto &bus_name: bus_names) {
						if (!bus_name.is_string()) {
							log_error("One of the names of %s is not a string.\n", bus_desc.str());
						}
						add_port(
							current_module,
							bus_name.string_value(),
							bus_type_width->bit_width,
							direction,
							!bus_type_width->downto,
							bus_type_width->downto ? bus_type_width->bit_to : bus_type_width->bit_from
						);
					}
				} else if (g.count("bundle")) {
					std::stringstream bundle_desc;
					bundle_desc << cell_desc << " bundle " << bundle_idx++;
					auto &bundle = get_object_attr(group_desc.str(), g, "bundle", empty_obj);

					// Determine direction
					std::string direction = "";
					if (bundle.count("direction")) {
						direction = get_string_attr(bundle_desc.str(), bundle, "direction", "input");
					} else {
						for_each_group(bundle_desc.str(), bundle, [&](const Json::object &sg) {
							if (!sg.count("pin")) {
								return;
							}
							auto pin = get_object_attr(bundle_desc.str() + " subgroup", sg, "pin", empty_obj);
							if (!pin.count("direction")) {
								return;
							}
							direction = get_string_attr(bundle_desc.str() + " pin", pin, "direction", "input");
						});
					}
					if (direction == "") {
						log_warning("No direction found for %s. Assuming input.\n", bundle_desc.str());
						direction = "input";
					}

					// Add ports for each member
					auto &members = get_array_attr(bundle_desc.str(), bundle, "members", empty_arr);
					for (auto &pin_name: members) {
						if (!pin_name.is_string()) {
							log_error("One of the members of %s is not a string.\n", bundle_desc.str());
						}
						add_port(current_module, pin_name.string_value(), 1, direction);
					}
				}
			});
		});
	}
} L2JFrontend;


YOSYS_NAMESPACE_END
