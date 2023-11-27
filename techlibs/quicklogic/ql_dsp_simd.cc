/*
 * Copyright 2020-2022 F4PGA Authors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * SPDX-License-Identifier: Apache-2.0
 */

#include "kernel/log.h"
#include "kernel/register.h"
#include "kernel/rtlil.h"
#include "kernel/sigtools.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

#define MODE_BITS_BASE_SIZE 80
#define MODE_BITS_EXTENSION_SIZE 13

// ============================================================================

struct QlDspSimdPass : public Pass {

	QlDspSimdPass() : Pass("ql_dsp_simd", "Infers QuickLogic k6n10f DSP pairs that can operate in SIMD mode") {}

	void help() override
	{
		log("\n");
		log("    ql_dsp_simd [selection]\n");
		log("\n");
		log("    This pass identifies k6n10f DSP cells with identical configuration\n");
		log("    and packs pairs of them together into other DSP cells that can\n");
		log("    perform SIMD operation.\n");
	}

	// ..........................................

	/// Describes DSP config unique to a whole DSP cell
	struct DspConfig {

		// Port connections
		dict<RTLIL::IdString, RTLIL::SigSpec> connections;

		// Whether DSPs pass configuration bits through ports of parameters
		bool use_cfg_params;

		// TODO: Possibly include parameters here. For now we have just
		// connections.

		DspConfig() = default;

		DspConfig(const DspConfig &ref) = default;
		DspConfig(DspConfig &&ref) = default;

		unsigned int hash() const { return connections.hash(); }

		bool operator==(const DspConfig &ref) const { return connections == ref.connections && use_cfg_params == ref.use_cfg_params; }
	};

	// ..........................................

	// DSP control and config ports to consider and how to map them to ports
	// of the target DSP cell
	const std::vector<std::pair<std::string, std::string>> m_DspCfgPorts = {std::make_pair("clock_i", "clk"),
																			std::make_pair("reset_i", "reset"),

																			std::make_pair("feedback_i", "feedback"),
																			std::make_pair("load_acc_i", "load_acc"),
																			std::make_pair("unsigned_a_i", "unsigned_a"),
																			std::make_pair("unsigned_b_i", "unsigned_b"),

																			std::make_pair("subtract_i", "subtract")};
	// For QL_DSP2 expand with configuration ports
	const std::vector<std::pair<std::string, std::string>> m_DspCfgPorts_expand = {
	  std::make_pair("output_select_i", "output_select"), std::make_pair("saturate_enable_i", "saturate_enable"),
	  std::make_pair("shift_right_i", "shift_right"), std::make_pair("round_i", "round"), std::make_pair("register_inputs_i", "register_inputs")};

	// For QL_DSP3 use parameters instead
	const std::vector<std::string> m_DspParams2Mode = {"OUTPUT_SELECT", "SATURATE_ENABLE", "SHIFT_RIGHT", "ROUND", "REGISTER_INPUTS"};

	// DSP data ports and how to map them to ports of the target DSP cell
	const std::vector<std::pair<std::string, std::string>> m_DspDataPorts = {
	  std::make_pair("a_i", "a"), std::make_pair("b_i", "b"),         std::make_pair("acc_fir_i", "acc_fir"),
	  std::make_pair("z_o", "z"), std::make_pair("dly_b_o", "dly_b"),
	};

	// DSP parameters
	const std::vector<std::string> m_DspParams = {"COEFF_3", "COEFF_2", "COEFF_1", "COEFF_0"};

	// Source DSP cell type (SISD)
	const std::string m_SisdDspType = "dsp_t1_10x9x32";
	// Suffix for DSP cell with configuration parameters
	const std::string m_SisdDspType_cfg_params_suffix = "_cfg_params";

	// Target DSP cell types for the SIMD mode
	const std::string m_SimdDspType_cfg_ports = "QL_DSP2";
	const std::string m_SimdDspType_cfg_params = "QL_DSP3";

	/// Temporary SigBit to SigBit helper map.
	SigMap m_SigMap;

	// ..........................................

	void execute(std::vector<std::string> a_Args, RTLIL::Design *a_Design) override
	{
		log_header(a_Design, "Executing QL_DSP_SIMD pass.\n");

		// Parse args
		extra_args(a_Args, 1, a_Design);

		// Process modules
		for (auto module : a_Design->selected_modules()) {

			// Setup the SigMap
			m_SigMap.clear();
			m_SigMap.set(module);

			// Assemble DSP cell groups
			dict<DspConfig, std::vector<RTLIL::Cell *>> groups;
			for (auto cell : module->selected_cells()) {

				// Check if this is a DSP cell we are looking for (type starts with m_SisdDspType)
				if (strncmp(cell->type.c_str(), RTLIL::escape_id(m_SisdDspType).c_str(), RTLIL::escape_id(m_SisdDspType).size()) != 0) {
					continue;
				}

				// Skip if it has the (* keep *) attribute set
				if (cell->has_keep_attr()) {
					continue;
				}

				// Add to a group
				const auto key = getDspConfig(cell);
				groups[key].push_back(cell);
			}

			std::vector<const RTLIL::Cell *> cellsToRemove;

			// Map cell pairs to the target DSP SIMD cell
			for (const auto &it : groups) {
				const auto &group = it.second;
				const auto &config = it.first;

				bool use_cfg_params = config.use_cfg_params;
				// Ensure an even number
				size_t count = group.size();
				if (count & 1)
					count--;

				// Map SIMD pairs
				for (size_t i = 0; i < count; i += 2) {
					const RTLIL::Cell *dsp_a = group[i];
					const RTLIL::Cell *dsp_b = group[i + 1];

					std::string name = stringf("simd%ld", i / 2);
					std::string SimdDspType;

					if (use_cfg_params)
						SimdDspType = m_SimdDspType_cfg_params;
					else
						SimdDspType = m_SimdDspType_cfg_ports;

					log(" SIMD: %s (%s) + %s (%s) => %s (%s)\n", RTLIL::unescape_id(dsp_a->name).c_str(), RTLIL::unescape_id(dsp_a->type).c_str(),
						RTLIL::unescape_id(dsp_b->name).c_str(), RTLIL::unescape_id(dsp_b->type).c_str(), RTLIL::unescape_id(name).c_str(),
						SimdDspType.c_str());

					// Create the new cell
					RTLIL::Cell *simd = module->addCell(RTLIL::escape_id(name), RTLIL::escape_id(SimdDspType));

					// Check if the target cell is known (important to know
					// its port widths)
					if (!simd->known()) {
						log_error(" The target cell type '%s' is not known!", SimdDspType.c_str());
					}

					std::vector<std::pair<std::string, std::string>> DspCfgPorts = m_DspCfgPorts;
					if (!use_cfg_params)
						DspCfgPorts.insert(DspCfgPorts.end(), m_DspCfgPorts_expand.begin(), m_DspCfgPorts_expand.end());

					// Connect common ports
					for (const auto &it : DspCfgPorts) {
						auto sport = RTLIL::escape_id(it.first);
						auto dport = RTLIL::escape_id(it.second);

						simd->setPort(dport, config.connections.at(sport));
					}

					// Connect data ports
					for (const auto &it : m_DspDataPorts) {
						auto sport = RTLIL::escape_id(it.first);
						auto dport = RTLIL::escape_id(it.second);

						size_t width;
						bool isOutput;

						std::tie(width, isOutput) = getPortInfo(simd, dport);

						auto getConnection = [&](const RTLIL::Cell *cell) {
							RTLIL::SigSpec sigspec;
							if (cell->hasPort(sport)) {
								const auto &sig = cell->getPort(sport);
								sigspec.append(sig);
							}
							if (sigspec.bits().size() < width / 2) {
								if (isOutput) {
									for (size_t i = 0; i < width / 2 - sigspec.bits().size(); ++i) {
										sigspec.append(RTLIL::SigSpec());
									}
								} else {
									sigspec.append(RTLIL::SigSpec(RTLIL::Sx, width / 2 - sigspec.bits().size()));
								}
							}
							return sigspec;
						};

						RTLIL::SigSpec sigspec;
						sigspec.append(getConnection(dsp_a));
						sigspec.append(getConnection(dsp_b));
						simd->setPort(dport, sigspec);
					}

					// Concatenate FIR coefficient parameters into the single
					// MODE_BITS parameter
					std::vector<RTLIL::State> mode_bits;
					for (const auto &it : m_DspParams) {
						auto val_a = dsp_a->getParam(RTLIL::escape_id(it));
						auto val_b = dsp_b->getParam(RTLIL::escape_id(it));

						mode_bits.insert(mode_bits.end(), val_a.begin(), val_a.end());
						mode_bits.insert(mode_bits.end(), val_b.begin(), val_b.end());
					}
					long unsigned int mode_bits_size = MODE_BITS_BASE_SIZE;
					if (use_cfg_params) {
						// Add additional config parameters if necessary
						mode_bits.push_back(RTLIL::S1); // MODE_BITS[80] == F_MODE : Enable fractured mode
						for (const auto &it : m_DspParams2Mode) {
							log_assert(dsp_a->getParam(RTLIL::escape_id(it)) == dsp_b->getParam(RTLIL::escape_id(it)));
							auto param = dsp_a->getParam(RTLIL::escape_id(it));
							if (param.size() > 1) {
								mode_bits.insert(mode_bits.end(), param.bits.begin(), param.bits.end());
							} else {
								mode_bits.push_back(param.bits[0]);
							}
						}
						mode_bits_size += MODE_BITS_EXTENSION_SIZE;
					} else {
						// Enable the fractured mode by connecting the control
						// port.
						simd->setPort(RTLIL::escape_id("f_mode"), RTLIL::S1);
					}
					simd->setParam(RTLIL::escape_id("MODE_BITS"), RTLIL::Const(mode_bits));
					log_assert(mode_bits.size() == mode_bits_size);

					// Handle the "is_inferred" attribute. If one of the fragments
					// is not inferred mark the whole DSP as not inferred
					bool is_inferred_a =
					  dsp_a->has_attribute(RTLIL::escape_id("is_inferred")) ? dsp_a->get_bool_attribute(RTLIL::escape_id("is_inferred")) : false;
					bool is_inferred_b =
					  dsp_b->has_attribute(RTLIL::escape_id("is_inferred")) ? dsp_b->get_bool_attribute(RTLIL::escape_id("is_inferred")) : false;

					simd->set_bool_attribute(RTLIL::escape_id("is_inferred"), is_inferred_a && is_inferred_b);

					// Mark DSP parts for removal
					cellsToRemove.push_back(dsp_a);
					cellsToRemove.push_back(dsp_b);
				}
			}

			// Remove old cells
			for (const auto &cell : cellsToRemove) {
				module->remove(const_cast<RTLIL::Cell *>(cell));
			}
		}

		// Clear
		m_SigMap.clear();
	}

	// ..........................................

	/// Looks up port width and direction in the cell definition and returns it.
	/// Returns (0, false) if it cannot be determined.
	std::pair<size_t, bool> getPortInfo(RTLIL::Cell *a_Cell, RTLIL::IdString a_Port)
	{
		if (!a_Cell->known()) {
			return std::make_pair(0, false);
		}

		// Get the module defining the cell (the previous condition ensures
		// that the pointers are valid)
		RTLIL::Module *mod = a_Cell->module->design->module(a_Cell->type);
		if (mod == nullptr) {
			return std::make_pair(0, false);
		}

		// Get the wire representing the port
		RTLIL::Wire *wire = mod->wire(a_Port);
		if (wire == nullptr) {
			return std::make_pair(0, false);
		}

		return std::make_pair(wire->width, wire->port_output);
	}

	/// Given a DSP cell populates and returns a DspConfig struct for it.
	DspConfig getDspConfig(RTLIL::Cell *a_Cell)
	{
		DspConfig config;

		string cell_type = a_Cell->type.str();
		string suffix = m_SisdDspType_cfg_params_suffix;

		bool use_cfg_params = cell_type.size() >= suffix.size() && 0 == cell_type.compare(cell_type.size() - suffix.size(), suffix.size(), suffix);

		std::vector<std::pair<std::string, std::string>> DspCfgPorts = m_DspCfgPorts;
		if (!use_cfg_params)
			DspCfgPorts.insert(DspCfgPorts.end(), m_DspCfgPorts_expand.begin(), m_DspCfgPorts_expand.end());

		config.use_cfg_params = use_cfg_params;

		for (const auto &it : DspCfgPorts) {
			auto port = RTLIL::escape_id(it.first);

			// Port unconnected
			if (!a_Cell->hasPort(port)) {
				config.connections[port] = RTLIL::SigSpec(RTLIL::Sx);
				continue;
			}

			// Get the port connection and map it to unique SigBits
			const auto &orgSigSpec = a_Cell->getPort(port);
			const auto &orgSigBits = orgSigSpec.bits();

			RTLIL::SigSpec newSigSpec;
			for (size_t i = 0; i < orgSigBits.size(); ++i) {
				auto newSigBit = m_SigMap(orgSigBits[i]);
				newSigSpec.append(newSigBit);
			}

			// Store
			config.connections[port] = newSigSpec;
		}

		return config;
	}

} QlDspSimdPass;

PRIVATE_NAMESPACE_END
