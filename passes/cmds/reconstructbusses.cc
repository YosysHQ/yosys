#include "kernel/sigtools.h"
#include "kernel/yosys.h"
#include <set>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct ReconstructBusses : public ScriptPass {
	ReconstructBusses() : ScriptPass("reconstructbusses", "Reconstruct busses from wires with the same prefix following the convention: <prefix>_<index>_") {}
	void script() override {}

	void execute(std::vector<std::string>, RTLIL::Design *design) override
	{
		if (design == nullptr) {
			log_error("No design object");
			return;
		}
		log("Running reconstructbusses pass\n");
		log_flush();
		for (auto module : design->modules()) {
			// Collect all wires with a common prefix
			dict<std::string, std::vector<RTLIL::Wire *>> wire_groups;
			for (auto wire : module->wires()) {
				if (wire->name[0] == '$') // Skip internal wires
					continue;
				std::string prefix = wire->name.str();

				if (prefix.empty())
					continue;
				// We want to truncate the final _<index>_ part of the string
				// Example: "add_Y_0_"
				// Result:  "add_Y"
				std::string::iterator end = prefix.end() - 1;
				if ((*end) == '_') {
					// Last character is an _, it is a bit blasted index
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

					std::string no_bitblast_prefix;
					std::copy(prefix.begin(), end, std::back_inserter(no_bitblast_prefix));
					wire_groups[no_bitblast_prefix].push_back(wire);
				}
			}
			std::map<std::string, RTLIL::Wire *> wirenames_to_remove;
			pool<RTLIL::Wire *> wires_to_remove;
			// Reconstruct vectors
			for (auto &it : wire_groups) {
				std::string prefix = it.first;
				std::vector<RTLIL::Wire *> &wires = it.second;

				// Sort wires by their bit index (assuming the suffix is _<index>_)
				std::sort(wires.begin(), wires.end(), [](RTLIL::Wire *a, RTLIL::Wire *b) {
					std::string a_name = a->name.str();
					std::string b_name = b->name.str();
					std::string::iterator a_end = a_name.end() - 1;
					std::string::iterator b_end = b_name.end() - 1;
					if (((*a_end) == '_') && ((*b_end) == '_')) {
						a_name = a_name.substr(0, a_name.size() - 1);
						b_name = b_name.substr(0, b_name.size() - 1);
						std::string a_index_str = a_name.substr(a_name.find_last_of('_') + 1);
						std::string b_index_str = b_name.substr(b_name.find_last_of('_') + 1);
						int a_index = std::stoi(a_index_str);
						int b_index = std::stoi(b_index_str);
						return a_index > b_index; // Descending order for correct concatenation
					} else {
						return false;
					}
				});

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

			// Reconnect cells
			for (auto cell : module->cells()) {
				for (auto &conn : cell->connections_) {
					RTLIL::SigSpec new_sig;
					bool modified = false;
					for (auto chunk : conn.second.chunks()) {
						// std::cout << "Port:" << conn.first.c_str() << std::endl;
						// std::cout << "Conn:" << chunk.wire->name.c_str() << std::endl;
						// Find the connections that match the wire group prefix
						std::string lhs_name = chunk.wire->name.c_str();
						std::map<std::string, RTLIL::Wire *>::iterator itr =  wirenames_to_remove.find(lhs_name);
						if (itr != wirenames_to_remove.end()) {
							std::string ch_name = chunk.wire->name.c_str();
							std::string::iterator ch_end = ch_name.end() - 1;
							if ((*ch_end) == '_') {
								ch_name = ch_name.substr(0, ch_name.size() - 1);
								std::string ch_index_str = ch_name.substr(ch_name.find_last_of('_') + 1);
								// std::cout << "ch_name: " << ch_name << std::endl;
								if (!ch_index_str.empty()) {
									// Create a new connection sigspec that matches the previous bit index
									int ch_index = std::stoi(ch_index_str);
									RTLIL::SigSpec bit = RTLIL::SigSpec(itr->second, ch_index, 1);
									new_sig.append(bit);
									modified = true;
								}
							}
						} else {
							new_sig.append(chunk);
							modified = true;
						}
					}
					// Replace the previous connection
					if (modified)
						conn.second = new_sig;
				}
			}

			// Reconnect top connections before removing the old wires
			// std::cout << "Wire to remove: " << wire_name << std::endl;
			for (auto &conn : module->connections()) {
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
					std::string conn_lhs = sub_lhs.wire->name.c_str();
					std::string conn_rhs = sub_rhs.wire->name.c_str();
					// The connection LHS matches a wire that is replaced by a bus
					// std::cout << "Conn: " << conn_lhs << " to: " << conn_rhs << std::endl;
					std::map<std::string, RTLIL::Wire *>::iterator itr =  wirenames_to_remove.find(conn_lhs);
					if (itr != wirenames_to_remove.end()) {
						std::string::iterator conn_lhs_end = conn_lhs.end() - 1;
						if ((*conn_lhs_end) == '_') {
							conn_lhs = conn_lhs.substr(0, conn_lhs.size() - 1);
							std::string ch_index_str = conn_lhs.substr(conn_lhs.find_last_of('_') + 1);
							if (!ch_index_str.empty()) {
								// std::cout << "Conn LHS: " << conn_lhs << std::endl;
								// std::string conn_rhs = sub_rhs.wire->name.c_str();
								// std::cout << "Conn RHS: " << conn_rhs << std::endl;
								int ch_index = std::stoi(ch_index_str);
								// Create the LHS sigspec of the desired bit
								RTLIL::SigSpec bit = RTLIL::SigSpec(itr->second, ch_index, 1);
								if (sub_rhs.size() > 1) {
									// If RHS has width > 1, replace with the bitblasted RHS corresponding to the
									// connected bit
									RTLIL::SigSpec rhs_bit = RTLIL::SigSpec(sub_rhs.wire, ch_index, 1);
									// And connect it
									module->connect(bit, rhs_bit);
								} else {
									// Else, directly connect
									module->connect(bit, sub_rhs);
								}
							}
						}
					}
					lit++;
					if (++rit != rhs.chunks().rend())
						rit++;
				}
			}

			// Remove old wires
			module->remove(wires_to_remove);
			// Update module port list
			module->fixup_ports();
		}
	}
} ReconstructBusses;

PRIVATE_NAMESPACE_END
