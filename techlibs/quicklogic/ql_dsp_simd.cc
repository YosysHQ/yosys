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


// ============================================================================

struct QlDspSimdPass : public Pass {

	QlDspSimdPass() : Pass("ql_dsp_simd", "merge QuickLogic K6N10f DSP pairs to operate in SIMD mode") {}

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    ql_dsp_simd [selection]\n");
		log("\n");
		log("This pass identifies K6N10f DSP cells with identical configuration and pack pairs\n");
		log("of them together into other DSP cells that can perform SIMD operation.\n");
	}

	// ..........................................

	/// Describes DSP config unique to a whole DSP cell
	struct DspConfig {
		// Port connections
		dict<RTLIL::IdString, RTLIL::SigSpec> connections;

		DspConfig() = default;

		DspConfig(const DspConfig &ref) = default;
		DspConfig(DspConfig &&ref) = default;

		unsigned int hash() const { return connections.hash(); }

		bool operator==(const DspConfig &ref) const { return connections == ref.connections; }
	};

	// ..........................................

	const size_t m_ModeBitsSize = 80;

	// DSP parameters
	const std::vector<std::string> m_DspParams = {"COEFF_3", "COEFF_2", "COEFF_1", "COEFF_0"};

	/// Temporary SigBit to SigBit helper map.
	SigMap sigmap;

	// ..........................................

	void execute(std::vector<std::string> a_Args, RTLIL::Design *a_Design) override
	{
		log_header(a_Design, "Executing QL_DSP_SIMD pass.\n");

		// DSP control and config ports to consider and how to map them to ports
		// of the target DSP cell
		static const std::vector<std::pair<IdString, IdString>> m_DspCfgPorts = {
			std::make_pair(ID(clock_i), ID(clk)),
			std::make_pair(ID(reset_i), ID(reset)),
			std::make_pair(ID(feedback_i), ID(feedback)),
			std::make_pair(ID(load_acc_i), ID(load_acc)),
			std::make_pair(ID(unsigned_a_i), ID(unsigned_a)),
			std::make_pair(ID(unsigned_b_i), ID(unsigned_b)),
			std::make_pair(ID(subtract_i), ID(subtract)),
			std::make_pair(ID(output_select_i), ID(output_select)),
			std::make_pair(ID(saturate_enable_i), ID(saturate_enable)),
			std::make_pair(ID(shift_right_i), ID(shift_right)),
			std::make_pair(ID(round_i), ID(round)),
			std::make_pair(ID(register_inputs_i), ID(register_inputs))
		};

		// DSP data ports and how to map them to ports of the target DSP cell
		static const std::vector<std::pair<IdString, IdString>> m_DspDataPorts = {
			std::make_pair(ID(a_i), ID(a)),
			std::make_pair(ID(b_i), ID(b)),
			std::make_pair(ID(acc_fir_i), ID(acc_fir)),
			std::make_pair(ID(z_o), ID(z)),
			std::make_pair(ID(dly_b_o), ID(dly_b))
		};

		// Source DSP cell type (SISD)
		static const IdString m_SisdDspType = ID(dsp_t1_10x9x32);

		// Target DSP cell types for the SIMD mode
		static const IdString m_SimdDspType = ID(QL_DSP2);

		// Parse args
		extra_args(a_Args, 1, a_Design);

		// Process modules
		for (auto module : a_Design->selected_modules()) {
			// Setup the SigMap
			sigmap.set(module);

			// Assemble DSP cell groups
			dict<DspConfig, std::vector<RTLIL::Cell *>> groups;
			for (auto cell : module->selected_cells()) {
				// Check if this is a DSP cell we are looking for (type starts with m_SisdDspType)
				if (cell->type != m_SisdDspType)
					continue;

				// Skip if it has the (* keep *) attribute set
				if (cell->has_keep_attr())
					continue;

				// Add to a group
				const auto key = getDspConfig(cell, m_DspCfgPorts);
				groups[key].push_back(cell);
			}

			std::vector<Cell *> cellsToRemove;

			// Map cell pairs to the target DSP SIMD cell
			for (const auto &it : groups) {
				const auto &group = it.second;
				const auto &config = it.first;

				// Ensure an even number
				size_t count = group.size();
				if (count & 1)
					count--;

				// Map SIMD pairs
				for (size_t i = 0; i < count; i += 2) {
					Cell *dsp_a = group[i];
					Cell *dsp_b = group[i + 1];

					// Create the new cell
					Cell *simd = module->addCell(NEW_ID, m_SimdDspType);

					log(" SIMD: %s (%s) + %s (%s) => %s (%s)\n", log_id(dsp_a), log_id(dsp_a->type),
						log_id(dsp_b), log_id(dsp_b->type), log_id(simd), log_id(simd->type));

					// Check if the target cell is known (important to know
					// its port widths)
					if (!simd->known())
						log_error(" The target cell type '%s' is not known!", log_id(simd));

					// Connect common ports
					for (const auto &it : m_DspCfgPorts)
						simd->setPort(it.first, config.connections.at(it.second));

					// Connect data ports
					for (const auto &it : m_DspDataPorts) {
						size_t width;
						bool isOutput;

						std::tie(width, isOutput) = getPortInfo(simd, it.second);

						auto getConnection = [&](const RTLIL::Cell *cell) {
							RTLIL::SigSpec sigspec;
							if (cell->hasPort(it.first)) {
								const auto &sig = cell->getPort(it.first);
								sigspec.append(sig);
							}

							int padding = width / 2 - sigspec.size();

							if (padding) {
								if (!isOutput)
									sigspec.append(RTLIL::SigSpec(RTLIL::Sx, padding));
								else
									sigspec.append(module->addWire(NEW_ID, padding));
							}
							return sigspec;
						};

						RTLIL::SigSpec sigspec;
						sigspec.append(getConnection(dsp_a));
						sigspec.append(getConnection(dsp_b));
						simd->setPort(it.second, sigspec);
					}

					// Concatenate FIR coefficient parameters into the single
					// MODE_BITS parameter
					Const mode_bits;
					for (const auto &it : m_DspParams) {
						auto val_a = dsp_a->getParam(it);
						auto val_b = dsp_b->getParam(it);

						mode_bits.bits().insert(mode_bits.bits().end(),
							val_a.begin(), val_a.end());
						mode_bits.bits().insert(mode_bits.bits().end(),
							val_b.begin(), val_b.end());
					}

					// Enable the fractured mode by connecting the control
					// port.
					simd->setPort(ID(f_mode), State::S1);
					simd->setParam(ID(MODE_BITS), mode_bits);
					log_assert(mode_bits.size() == m_ModeBitsSize);

					// Handle the "is_inferred" attribute. If one of the fragments
					// is not inferred mark the whole DSP as not inferred
					bool is_inferred_a = dsp_a->get_bool_attribute(ID(is_inferred));
					bool is_inferred_b = dsp_b->get_bool_attribute(ID(is_inferred));
					simd->set_bool_attribute(ID(is_inferred), is_inferred_a && is_inferred_b);

					// Mark DSP parts for removal
					cellsToRemove.push_back(dsp_a);
					cellsToRemove.push_back(dsp_b);
				}
			}

			// Remove old cells
			for (auto cell : cellsToRemove)
				module->remove(cell);
		}
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
	DspConfig getDspConfig(RTLIL::Cell *a_Cell, const std::vector<std::pair<IdString, IdString>> &dspCfgPorts)
	{
		DspConfig config;

		for (const auto &it : dspCfgPorts) {
			auto port = it.first;

			// Port unconnected
			if (!a_Cell->hasPort(port))
				continue;

			config.connections[port] = sigmap(a_Cell->getPort(port));
		}

		return config;
	}
} QlDspSimdPass;

PRIVATE_NAMESPACE_END
