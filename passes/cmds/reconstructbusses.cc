#include "kernel/sigtools.h"
#include "kernel/yosys.h"
#include <set>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct ReconstructBusses : public ScriptPass {
	ReconstructBusses()
	    : ScriptPass("reconstructbusses", "Reconstruct busses from wires with the same prefix following the convention: <prefix>_<index>_")
	{
	}
	void script() override {}

	bool is_digits(const std::string &str) { return std::all_of(str.begin(), str.end(), ::isdigit); }

	// Get the index <index> from the signal name "prefix_<index>_"
	int getIndex(std::string name, std::map<std::string, RTLIL::Wire *> &wirenames_to_remove)
	{
		std::map<std::string, RTLIL::Wire *>::iterator itr_lhs = wirenames_to_remove.find(name);
		if (itr_lhs != wirenames_to_remove.end()) {
			std::string::iterator conn_lhs_end = name.end() - 1;
			if ((*conn_lhs_end) == '_') {
				name = name.substr(0, name.size() - 1);
				if (name.find("_") != std::string::npos) {
					std::string ch_index_str = name.substr(name.find_last_of('_') + 1);
					if (!ch_index_str.empty() && is_digits(ch_index_str)) {
						int ch_index = std::stoi(ch_index_str);
						return ch_index;
					}
				}
			}
		}
		return -1;
	}

	void execute(std::vector<std::string>, RTLIL::Design *design) override
	{
		if (design == nullptr) {
			log_error("No design object");
			return;
		}
		bool debug = false;
		if (std::getenv("DEBUG_RECONSTRUCT_BUSSES")) {
			debug = true;
		}
		log("Running reconstructbusses pass\n");
		log_flush();
		for (auto module : design->modules()) {
			log("Creating bus groups for module %s\n", module->name.str().c_str());
			log_flush();
			// Collect all wires with a common prefix
			dict<std::string, std::vector<RTLIL::Wire *>> wire_groups;
			for (auto wire : module->wires()) {
				if (wire->name[0] == '$') // Skip internal wires
					continue;
				if ((!wire->port_input) && (!wire->port_output)) {
					continue;
				}
				std::string prefix = wire->name.str();

				if (prefix.empty())
					continue;
				// We want to truncate the final _<index>_ part of the string
				// Example: "add_Y_0_"
				// Result:  "add_Y"
				std::string::iterator end = prefix.end() - 1;
				if ((*end) == '_') {
					// Last character is an _, check that it is a bit blasted index:
					bool valid_index = false;
					std::string ch_name = prefix.substr(0, prefix.size() - 1);
					if (ch_name.find("_") != std::string::npos) {
						std::string ch_index_str = ch_name.substr(ch_name.find_last_of('_') + 1);
						if ((!ch_index_str.empty() && is_digits(ch_index_str))) {
							valid_index = true;
						}
					}
					if (!valid_index) {
						log_warning("Invalid net name %s\n", prefix.c_str());
						log_flush();
						continue;
					}

					end--;
					for (; end != prefix.begin(); end--) {
						if ((*end) != '_') {
							// Truncate until the next _
							continue;
						} else {
							// Truncate the _
							break;
						}
					}
					if (end == prefix.begin()) {
						// Last _ didn't mean there was another _
						log_warning("Invalid net name %s\n", prefix.c_str());
						log_flush();
						continue;
					}
					std::string no_bitblast_prefix;
					std::copy(prefix.begin(), end, std::back_inserter(no_bitblast_prefix));
					wire_groups[no_bitblast_prefix].push_back(wire);
				}
			}
			log("Found %ld groups\n", wire_groups.size());
			if (wire_groups.size() == 0) {
				std::cout << "No busses to reconstruct. Done." << std::endl;
				return;
			}
			log("Creating busses\n");
			log_flush();
			std::map<std::string, RTLIL::Wire *> wirenames_to_remove;
			pool<RTLIL::Wire *> wires_to_remove;
			// Reconstruct vectors
			for (auto &it : wire_groups) {
				std::string prefix = it.first;
				if (debug)
					std::cout << "Wire group:" << prefix << std::endl;
				std::vector<RTLIL::Wire *> &wires = it.second;

				// Create a new vector wire
				int width = wires.size();
				RTLIL::Wire *new_wire = module->addWire(prefix, width);
				for (RTLIL::Wire *w : wires) {
					// All wires in the same wire_group are of the same type (input_port, output_port or none)
					if (w->port_input)
						new_wire->port_input = 1;
					else if (w->port_output)
						new_wire->port_output = 1;
					break;
				}

				for (auto wire : wires) {
					std::string wire_name = wire->name.c_str();
					wirenames_to_remove.emplace(wire_name, new_wire);
					wires_to_remove.insert(wire);
				}
			}
			log("Reconnecting cells\n");
			log_flush();
			// Reconnect cells
			for (auto cell : module->cells()) {
				if (debug)
					std::cout << "Cell:" << cell->name.c_str() << std::endl;
				for (auto &conn : cell->connections_) {
					RTLIL::SigSpec new_sig;
					bool modified = false;
					for (auto chunk : conn.second.chunks()) {
						if (debug) {
							std::cout << "  Port:" << conn.first.c_str() << std::endl;
							std::cout << "  Conn:" << (chunk.wire ? chunk.wire->name.c_str() : "constant") << std::endl;
						}
						// Find the connections that match the wire group prefix
						if (chunk.wire == nullptr) {
							continue;
						}
						std::string lhs_name = chunk.wire ? chunk.wire->name.c_str() : "";
						int lhsIndex = getIndex(lhs_name, wirenames_to_remove);
						std::map<std::string, RTLIL::Wire *>::iterator itr_lhs = wirenames_to_remove.find(lhs_name);
						if (itr_lhs != wirenames_to_remove.end()) {
							if (lhsIndex >= 0) {
								// Create a new connection sigspec that matches the previous
								// bit index
								if (lhsIndex < itr_lhs->second->width) {
									RTLIL::SigSpec bit = RTLIL::SigSpec(itr_lhs->second, lhsIndex, 1);
									new_sig.append(bit);
									modified = true;
								} else {
									log_warning("Attempting to reconnect cell %s, port: %s of size %d with out-of-bound index %d\n",
										cell->name.c_str(),
										conn.first.c_str(),
										itr_lhs->second->width, lhsIndex);
									for (RTLIL::Wire *w : wires_to_remove) {
										if (strcmp(w->name.c_str(), itr_lhs->second->name.c_str()) == 0) {
											wires_to_remove.erase(w);
											break;
										}
									}
								}
							} else {
								new_sig.append(chunk);
								modified = true;
							}
						}
					}
					// Replace the previous connection
					if (modified)
						conn.second = new_sig;
				}
			}
			if (debug)
				run_pass("write_rtlil post_reconnect_cells.rtlil");
			log("Reconnecting top connections\n");
			log_flush();
			// Reconnect top connections before removing the old wires
			std::vector<RTLIL::SigSig> newConnections;
			for (auto &conn : module->connections()) {
				// Keep all the connections that won't get rewired
				newConnections.push_back(conn);
			}
			for (auto &conn : newConnections) {
				RTLIL::SigSpec lhs = conn.first;
				RTLIL::SigSpec rhs = conn.second;
				auto lit = lhs.chunks().rbegin();
				if (lit == lhs.chunks().rend())
					continue;
				auto rit = rhs.chunks().rbegin();
				if (rit == rhs.chunks().rend())
					continue;
				RTLIL::SigChunk sub_rhs = *rit;
				while (lit != lhs.chunks().rend()) {
					RTLIL::SigChunk sub_lhs = *lit;
					std::string conn_lhs_s = sub_lhs.wire ? sub_lhs.wire->name.c_str() : "";
					std::string conn_rhs_s = sub_rhs.wire ? sub_rhs.wire->name.c_str() : "";
					if (!conn_lhs_s.empty()) {
						if (debug) {
							std::cout << "Conn LHS: " << conn_lhs_s << std::endl;
							std::cout << "Conn RHS: " << conn_rhs_s << std::endl;
						}
						int lhsIndex = getIndex(conn_lhs_s, wirenames_to_remove);
						int rhsIndex = getIndex(conn_rhs_s, wirenames_to_remove);
						std::map<std::string, RTLIL::Wire *>::iterator itr_lhs = wirenames_to_remove.find(conn_lhs_s);
						std::map<std::string, RTLIL::Wire *>::iterator itr_rhs = wirenames_to_remove.find(conn_rhs_s);
						if (itr_lhs != wirenames_to_remove.end() || itr_rhs != wirenames_to_remove.end()) {
							if (lhsIndex >= 0) {
								RTLIL::SigSpec lbit;
								// Create the LHS sigspec of the desired bit
								if (lhsIndex < itr_lhs->second->width) {
									lbit = RTLIL::SigSpec(itr_lhs->second, lhsIndex, 1);
								} else {
									lbit = itr_lhs->second;
									log_warning("Attempting to reconnect signal %s, of "
												    "size %d with out-of-bound index %d\n",
												    conn_lhs_s.c_str(),
												    itr_lhs->second->width, lhsIndex);
									for (RTLIL::Wire *w : wires_to_remove) {
										if (strcmp(w->name.c_str(),conn_lhs_s.c_str()) == 0) {
											wires_to_remove.erase(w);
											break;
										}
									}
								}
								if (sub_rhs.size() > 1) {
									// If RHS has width > 1, replace with the bitblasted RHS
									// corresponding to the connected bit
									if (lhsIndex < sub_rhs.wire->width) {
										RTLIL::SigSpec rhs_bit = RTLIL::SigSpec(sub_rhs.wire, lhsIndex, 1);
										// And connect it
										module->connect(lbit, rhs_bit);
									} else {
										log_warning("Attempting to reconnect signal %s, of "
												    "size %d with out-of-bound index %d\n",
												    conn_rhs_s.c_str(),
												    sub_rhs.wire->width, lhsIndex);
										for (RTLIL::Wire *w : wires_to_remove) {
											if (strcmp(w->name.c_str(), conn_rhs_s.c_str()) == 0) {
												wires_to_remove.erase(w);
												break;
											}
										}
									}
								} else {
									// Else, directly connect
									if (rhsIndex >= 0) {
										if (rhsIndex < itr_rhs->second->width) {
											RTLIL::SigSpec rbit =
											  RTLIL::SigSpec(itr_rhs->second, rhsIndex, 1);
											module->connect(lbit, rbit);
										} else {
											log_warning("Attempting to reconnect signal %s, of "
												    "size %d with out-of-bound index %d\n",
												    conn_lhs_s.c_str(),
												    itr_lhs->second->width, rhsIndex);
											for (RTLIL::Wire *w : wires_to_remove) {
												if (strcmp(w->name.c_str(), conn_lhs_s.c_str()) == 0) {
													wires_to_remove.erase(w);
													break;
												}
											}
										}
									} else {
										module->connect(lbit, sub_rhs);
									}
								}
							} else {
								// Else, directly connect
								RTLIL::SigSpec bit = RTLIL::SigSpec(itr_lhs->second, 0, 1);
								module->connect(bit, sub_rhs);
							}
						}
					}
					lit++;
					if (++rit != rhs.chunks().rend())
						rit++;
				}
			}
			if (debug)
				run_pass("write_rtlil post_reconnect_top.rtlil");
			// Remove old bit blasted wires
			// Cleans the dangling connections too
			log("Removing bit blasted wires\n");
			log_flush();
			if (debug) {
				for (RTLIL::Wire* w : wires_to_remove) {
					std::cout << "  " << w->name.c_str() << std::endl;
				}
			}
			module->remove(wires_to_remove);
			// Update module port list
			log("Re-creating ports\n");
			log_flush();
			module->fixup_ports();
		}
		if (debug)
			run_pass("write_rtlil post_reconstructbusses.rtlil");
		log("End reconstructbusses pass\n");
		log_flush();
	}
} ReconstructBusses;

PRIVATE_NAMESPACE_END
