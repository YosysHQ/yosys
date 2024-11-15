/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
 *                2024  Alain Dargelas    <alain@silimate.com>
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

#include "kernel/yosys.h"
#include "kernel/sigtools.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct ActivityProp {
	Module *module;
	SigMap sigmap;
	uint32_t nbBitsWithActivity = 0;

	// Split a string based on separator, returns a vector of tokens as reference argument
	// If skipEmpty is true, return "" for string "    ", when separator is " "
	void tokenize(std::string_view str, std::string_view separator, std::vector<std::string> &result, bool skipEmpty)
	{
		std::string::size_type pos{0};
		const auto sepSize = separator.size();
		const auto stringSize = str.size();
		std::string tmp;
		std::string::size_type n = str.find(separator, pos);
		while (n != std::string::npos) {
			tmp = str.substr(pos, n - pos);
			if (!(tmp.empty() && skipEmpty))
				result.push_back(tmp);
			pos = n + sepSize;
			n = str.find(separator, pos);
		}
		if (pos < stringSize) { // put last part
			tmp = str.substr(pos, stringSize - pos);
			if (!(tmp.empty() && skipEmpty))
				result.push_back(tmp);
		}
	}

	// Split a string based on separator, returns a vector of tokens
	// If skipEmpty is true, return "" for string "    ", when separator is " "
	std::vector<std::string> tokenize(std::string_view str, std::string_view separator, bool skipEmpty)
	{
		std::vector<std::string> result;
		tokenize(str, separator, result, skipEmpty);
		return result;
	}

	ActivityProp(Module *module) : module(module), sigmap(module)
	{
		std::map<SigBit, std::string> ActivityMap;
		std::map<SigBit, std::string> DutyMap;
		// Build {signal bit - activity} map from the wire activities calculated in the sim pass
		for (Wire *wire : module->wires()) {
			SigSpec sig(sigmap(wire));
			// Retrieve the activity/dutycycle attributes created in the sim pass, attached to wires, in the form:
			// $ACKT: 0.1 0.2 .... (Each bit in a bus has its own activity, index 0 of the bus is left most)
			std::string act = wire->get_string_attribute("$ACKT");
			std::string duty = wire->get_string_attribute("$DUTY");
			//std::cout << "WIRE: " << wire->name.c_str() << " act: " << act << std::endl;
			// Split the activity lists
			std::vector<std::string> activities = tokenize(act, " ", true);
			std::vector<std::string> duties = tokenize(duty, " ", true);
			// Assign them to each SigBit (1 signal bit)
			for (uint32_t i = 0; i < (uint32_t)GetSize(sig); i++) {
				SigBit bit(sig[i]);
				if (i < activities.size()) {
					ActivityMap.emplace(bit, activities[i]);
					DutyMap.emplace(bit, duties[i]);
					nbBitsWithActivity++;
				} else {
					log_warning("Zeroing out activity for module: %s, wire: %s, wire_size: %d, activ_size: %ld\n",
						module->name.c_str(), wire->name.c_str(), GetSize(sig), activities.size());
					ActivityMap.emplace(bit, "0.0");
					DutyMap.emplace(bit, "0.0");
				}
			}
		}
		// Attach port activity to cell using sigmap
		for (auto cell : module->cells()) {
			std::string cell_ports_activity;
			std::string cell_ports_duty;
			for (auto conn : cell->connections()) {
				// Recombine individual bit activities for all cell ports into a list attached to the cell
				for (int i = 0; i < GetSize(conn.second); i++) {
					SigBit bit(sigmap(conn.second[i]));
					std::string port_name = std::string(conn.first.c_str()) + "[" + std::to_string(i) + "]";
					{
						std::map<SigBit, std::string>::iterator itr = ActivityMap.find(bit);
						if (itr != ActivityMap.end()) {
							cell_ports_activity += port_name + "=" + (*itr).second + " ";
						} else {
							RTLIL::SigSpec sigspec(bit);
							if (!sigspec.is_fully_const()) {
							  log_warning("No activity found for : %s/%s/%s\n", module->name.c_str(), cell->name.c_str(), port_name.c_str());
							}
							// constants have no activity
							cell_ports_activity += port_name + "=" + "0.0 ";
						}
					}
					{
						std::map<SigBit, std::string>::iterator itr = DutyMap.find(bit);
						if (itr != DutyMap.end()) {
							cell_ports_duty += port_name + "=" + (*itr).second + " ";
						} else {
							RTLIL::SigSpec sigspec(bit);
							if (!sigspec.is_fully_const()) {
							  log_warning("No dutycycle found for : %s/%s/%s\n", module->name.c_str(), cell->name.c_str(), port_name.c_str());
							}
							// constant 1 has duty cycle 1, constant 0 has duty cycle 0
							cell_ports_duty += port_name + "=" + (sigspec.as_bool() ? "1.0" : "0.0") + " ";
						}
					}
				}
			}
			// Annotate on cells the complete list of ports activities and dutycycles in the form:
			// $ACKT: \P1=0.1 \P2=0.2 ....
			cell->set_string_attribute("$ACKT:", cell_ports_activity);
			cell->set_string_attribute("$DUTY:", cell_ports_duty);
		}
	}

	uint32_t getNbBitsWithActivity() { return nbBitsWithActivity; }
};

struct ActivityClear {
	Module *module;

	ActivityClear(Module *module) : module(module)
	{
		for (Wire *wire : module->wires()) {
			wire->set_string_attribute("$ACKT", "");
			wire->set_string_attribute("$DUTY", "");
		}
		for (auto cell : module->cells()) {
			cell->set_string_attribute("$ACKT:", "");
			cell->set_string_attribute("$DUTY:", "");
		}
	}
};

struct ActivityPropPass : public Pass {
	ActivityPropPass() : Pass("activity_prop", "Attaches wire activity to cell ports") {}
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    activity_prop\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing Activity propagation pass\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			// No options currently. When adding in the future make sure to update docstring with [options]
			break;
		}
		extra_args(args, argidx, design);
		uint32_t totalNbBitsWithActivity = 0;
		for (auto module : design->modules()) {
			ActivityProp worker(module);
			totalNbBitsWithActivity += worker.getNbBitsWithActivity();
		}
		log("Collected %d bits with activity", totalNbBitsWithActivity);
		log_flush();
	}
} ActivityPropPass;

struct ActivityClearPass : public Pass {
	ActivityClearPass() : Pass("activity_clear", "Clears activity attached to cells and wires") {}
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    activity_clear\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing Activity clearing pass\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			// No options currently. When adding in the future make sure to update docstring with [options]
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->modules()) {
			ActivityClear worker(module);
		}
	}
} ActivityClearPass;


PRIVATE_NAMESPACE_END
