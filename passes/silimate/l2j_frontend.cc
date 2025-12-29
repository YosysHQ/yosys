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

#include "libs/nlohmann_json/json.hpp"
#include <stdexcept>

using namespace std::literals::string_literals;

YOSYS_NAMESPACE_BEGIN

using nlohmann::json;

/// @brief Gets an attribute as a double-width floating point number, or if the
///        key is undefined, returns a default value. If the attribute exists
///        but is a string, an attempt is made to parse a numeric value out of
///        the string.
/// @param o The container object
/// @param key The key used to access the attribute in question
/// @param default_ The fallback default value
/// @return the numeric attribute if found or the default otherwise
/// @throws json::type_error if the attribute exists, but is not either a number
///         or a string that can be parsed as a number.
inline double get_or_parse_number(const json &o, std::string key, double default_) {
	if (!o.count(key)) {
		return default_;
	}
	auto number = o[key];
	if (number.is_string()) {
		double parsed;
		auto raw = number.get<std::string>();
		std::stringstream parse(raw);
		parse >> parsed;
		if (parse.fail()) {
			throw std::invalid_argument(stringf("failed to parse number '%s' provided as a string", raw.c_str()));
		} else {
			return parsed;
		}
	}
	return number.get<double>();
}

/// @brief Gets an attribute as an boolean, or if the key is undefined,
///        returns a default value. If the attribute exists but is not a
///        boolean, it emulates the behavior of the Python programming language
///        as to "truthiness."
/// @param o The container object
/// @param key The key used to access the attribute in question
/// @param default_ The fallback default value
/// @return the boolean attribute if found or the default otherwise
inline bool value_as_boolean(const json &o, std::string key, bool default_) {
	if (!o.count(key)) {
		return default_;
	}
	json boolean = o[key];

	switch (boolean.type()) {
	case json::value_t::boolean:
		return boolean.get<bool>();
	case json::value_t::number_integer:
	case json::value_t::number_unsigned:
	case json::value_t::number_float:
		return bool(boolean.get<double>());
	case json::value_t::string:
		return bool(boolean.get<std::string>().length());
	case json::value_t::array:
	case json::value_t::object:
	case json::value_t::binary:
		return bool(boolean.size());
	case json::value_t::null:
	case json::value_t::discarded:
		return false;
	}
}


/// @brief Returns the first object of the .names array attribute of a given
///        string.
/// @param named_object The container in question
/// @return The first name if both the .names array attribute and the name itself
///         both exist, otherwise nullopt
/// @throws json::type_error if the object exists and is not an array, or
///         if the first element is not a string
inline std::optional<std::string> single_name_of(const json &named_object) {
	auto names = named_object.value<json::array_t>("names", {});
	if (!names.size()) {
		return std::nullopt;
	}
	return names[0].get<std::string>();
}

/// @brief Iterates over the .groups attribute of JSON objects.
///        If the attribute doesn't exist, it iterates over nothing.
/// @param o The container object
/// @param executor The lambda to execute that takes a constant reference to the
///        JSON object representing the group.
/// @throws json::type_error if .groups exists but is not an array, and if any
///         of .groups' elements are not objects.
inline void for_each_group(const json &j, std::function<void(const json &)> executor) {
	const auto groups = j.value<json::array_t>("groups", {});
	for (const json &group: groups) {
		executor(group.get<json::object_t>());
	}
}

// TypeWidth object (dynamic in the original Python)
struct TypeWidth {
	bool downto;
	int bit_from;
	int bit_to;
	int bit_width;

	/// @brief Constructs a TypeWidth declaration object from its JSON equivalent
	///        cell.
	/// @param type The type JSON object
	/// @return newly constructed type-width object
	/// @throws json::type_error if bit_from, bit_to, and bit_width exist and are
	///         not integers
	static TypeWidth from_json_object(const json &type) {
		auto downto = value_as_boolean(type, "downto", false);
		auto bit_from = type.value<int>("bit_from", 0);
		auto bit_to = type.value<int>("bit_to", 0);
		auto bit_width = type.value<int>("bit_width", (bit_from - bit_to) + 1);
		return TypeWidth { downto, bit_from, bit_to, bit_width };
	}

	/// @brief Collects and constructs TypeWidth objects from a container, be it
	///        either types declared in the top-level library or types local to a
	///        cell.
	/// @param container The JSON object containing types
	/// @return A mapping from the types' names to their newly constructed
	///         TypeWidth objects.
	/// @throws json::type_error if any of the groups have a .type that is not an
	///         object, or the object itself has .bit_from, .bit_to, and
	///         .bit_width values that exist and are not integers
	static auto collect_types(const json &container) {
		dict<std::string, TypeWidth> result;
		for_each_group(container, [&](const json &g){
			if (!g.count("type")) {
				return;
			}
			const auto type = g.value<json::object_t>("type", {});
			auto type_name = single_name_of(type);
			if (!type_name) {
				log_warning("Nameless type encountered\n");
				return;
			}
			result[*type_name] = TypeWidth::from_json_object(type);
		});
		return result;
	}
};


/// @brief For a bus or bundle object, attempts to get the direction from a
///        top-level .direction attribute or a .direction attribute of any of
///        the pins, falling back to "input" otherwise.
/// @param bus_or_bundle The bus or bundle object in question
/// @return A string representing the direction
/// @throws json::type_error if:
///         - the top-level .direction attribute exists and is not a string
///  				- the top-level .direction attribute does not exist and:
///           - any of the groups within the bus or bundle are not objects
///           - any of the .pin attributes of said groups are not objects
///           - any of the .direction attributes are not strings.
static auto get_bus_bundle_direction(const json &bus_or_bundle) {
	std::string direction = "";
	if (bus_or_bundle.count("direction")) {
		direction = bus_or_bundle["direction"].get<std::string>();
	} else {
		for_each_group(bus_or_bundle, [&](const json &sg) {
			if (!sg.count("pin")) {
				return;
			}
			const json pin = sg["pin"].get<json::object_t>();
			if (!pin.count("direction")) {
				return;
			}
			direction = pin["direction"].get<std::string>();
		});
	}
	if (direction == "") {
		log_warning("No direction found for bus or bundle. Assuming input...\n");
		direction = "input";
	}
	return direction;
}

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

		try {
		auto top_j = json::parse(*f);

		const json library = top_j["library"].get<json::object_t>();

		std::string leakage_power_unit = library.value<std::string>("leakage_power_unit", "1pW");

		// Group processing, part 1: record global bus type widths
		dict<std::string, TypeWidth> type_widths = TypeWidth::collect_types(library);

		// Group processing, part 2: create blackbox modules
		pool<IdString> already_defined;
		for_each_group(library, [&](const json &g) {
			if (!g.count("cell")) {
				return;
			}
			const json cell = g["cell"].get<json::object_t>();

			auto cell_name = single_name_of(cell);
			if (!cell_name) {
				log_warning("Nameless cell encountered.\n");
				return;
			}

			IdString module_name { "\\"s + *cell_name };
			if (already_defined.count(module_name)) {
				log_warning("Library cell already defined: %s\n", cell_name->c_str());
				return;
			}
			already_defined.insert(module_name);

			dict<std::string, TypeWidth> local_type_widths = TypeWidth::collect_types(cell);

			// Memory and stdcell
			bool is_memory = false, is_stdcell = true;
			bool dont_touch = value_as_boolean(cell, "dont_touch", false);
			bool dont_use = value_as_boolean(cell, "dont_use", false);
			if (dont_touch || dont_use) {
				is_stdcell = false;
			}
			for_each_group(cell, [&](const json &g) {
				if (g.count("memory")) {
					is_memory = true; is_stdcell = false;
				}
			});

			// PPA Numbers (TODO: add dynamic power data)
			auto area = get_or_parse_number(cell, "area", 0);
			auto cell_leakage_power = get_or_parse_number(cell, "cell_leakage_power", 0);

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

			if (cell.count("src")) {
				current_module->set_src_attribute(cell["src"].get<std::string>());
			}

			for_each_group(cell, [&](const json &g) {
				if (g.count("pin")) {
					const json pin = g["pin"].get<json::object_t>();
					const auto direction = pin.value<std::string>("direction", "input");
					const auto pin_names = pin.value<json::array_t>("names", {});
					for (auto &pin_name: pin_names) {
						add_port(current_module, pin_name.get<std::string>(), 1, direction);
					}
				} else if (g.count("bus")) {
					const json bus = g["bus"].get<json::object_t>();

					auto direction = get_bus_bundle_direction(bus);

					auto bus_type = bus.value<std::string>("bus_type", "");
					TypeWidth *bus_type_width = nullptr;
					if (type_widths.count(bus_type)) {
						bus_type_width = &type_widths[bus_type];
					} else if (local_type_widths.count(bus_type)) {
						bus_type_width = &local_type_widths[bus_type];
					} else {
						// bus_type_width = &default_type_width; // <-- possible alternate route
						log_warning("No type '%s' found for bus - skipping\n", bus_type);
						return;
					}
					for (auto &bus_name: bus.value<json::array_t>("names", {})) {
						add_port(
							current_module,
							bus_name.get<std::string>(),
							bus_type_width->bit_width,
							direction,
							!bus_type_width->downto,
							bus_type_width->downto ? bus_type_width->bit_to : bus_type_width->bit_from
						);
					}
				} else if (g.count("bundle")) {
					const json bundle = g["bundle"].get<json::object_t>();

					auto direction = get_bus_bundle_direction(bundle);

					for (auto &pin_name: bundle.value<json::array_t>("members", {})) {
						add_port(current_module, pin_name.get<std::string>(), 1, direction);
					}
				}
			});
		});
		} catch (json::parse_error &e) {
			log_error("Failed to parse liberty json file: %s\n", e.what());
		} catch (json::type_error &e) {
			log_error("Failed to import liberty json file: %s\n", e.what());
		} catch (std::invalid_argument &e) {
			log_error("Failed to import liberty json file: %s\n", e.what());
		}
	}
} L2JFrontend;


YOSYS_NAMESPACE_END
