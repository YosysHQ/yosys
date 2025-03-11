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

	QlDspSimdPass() : Pass("ql_dsp_simd", "merge QuickLogic K6N10f DSP pairs to operate in fractured mode") {}

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    ql_dsp_simd [selection]\n");
		log("\n");
		log("This pass identifies K6N10f DSP cells with identical configuration and merges\n");
		log("pairs of them, enabling fractured mode.\n");
	}

	// ..........................................

	/// Describes DSP config unique to a DSP cell
	struct DspConfig {
		// Port connections
		dict<RTLIL::IdString, RTLIL::SigSpec> connections;
		dict<RTLIL::IdString, RTLIL::Const> parameters;

		DspConfig() = default;

		DspConfig(const DspConfig &ref) = default;
		DspConfig(DspConfig &&ref) = default;

		[[nodiscard]] Hasher hash_into(Hasher h) const { h.eat(connections); return h; }

		bool operator==(const DspConfig &ref) const { return connections == ref.connections && parameters == ref.parameters; }
	};

	// ..........................................

	/// Temporary SigBit to SigBit helper map.
	SigMap sigmap;

	static bool is_cascade(const Cell* cell)
	{
		static const std::vector<IdString> cascade_ports = {
			ID(a_cout_o),
			ID(b_cout_o),
			ID(z_cout_o),
			ID(a_cin_i),
			ID(b_cin_i),
			ID(z_cin_i)
		};
		for (auto p : cascade_ports) {
			if (cell->hasPort(p) && !cell->getPort(p).is_fully_undef())
				return true;
		}
		return false;
	}
	// ..........................................

	void execute(std::vector<std::string> a_Args, RTLIL::Design *a_Design) override
	{
		log_header(a_Design, "Executing QL_DSP_SIMD pass.\n");

		// The following lists have to match simulation model interfaces.

		// DSP control and config ports that must be equal between
		// merged half-blocks
		// In addition to functional differences,
		// v1 and v2 have different balance between shared functionality
		// in ports vs params.
		static const std::vector<IdString> m_Dspv1CfgPorts = {
			ID(acc_fir_i),
			ID(feedback_i),
			ID(load_acc_i),
			ID(unsigned_a_i),
			ID(unsigned_b_i),
			ID(clock_i),
			ID(s_reset),
			ID(saturate_enable_i),
			ID(output_select_i),
			ID(round_i),
			ID(shift_right_i),
			ID(subtract_i),
			ID(register_inputs_i),
		};
		static const std::vector<IdString> m_Dspv1CfgParams = {
			ID(COEFF_0),
			ID(COEFF_1),
			ID(COEFF_2),
			ID(COEFF_3),
		};
		static const std::vector<IdString> m_Dspv2CfgPorts = {
			ID(clock_i),
			ID(reset_i),
			ID(acc_reset_i),
			ID(feedback_i),
			ID(load_acc_i),
			ID(output_select_i),
		};
		static const std::vector<IdString> m_Dspv2CfgParams = {
			ID(COEFF_0),
			ID(ACC_FIR),
			ID(ROUND),
			ID(ZC_SHIFT),
			ID(ZREG_SHIFT),
			ID(SHIFT_REG),
			ID(SATURATE),
			ID(SUBTRACT),
			ID(PRE_ADD),
			ID(A_SEL),
			ID(A_REG),
			ID(B_SEL),
			ID(B_REG),
			ID(C_REG),
			ID(BC_REG),
			ID(M_REG),
			ID(FRAC_MODE),
		};


		// Data ports to be concatenated into merged cell
		static const std::vector<IdString> m_Dspv1DataPorts = {
			ID(a_i),
			ID(b_i),
			ID(z_o),
			ID(dly_b_o),
		};
		static const std::vector<IdString> m_Dspv2DataPorts = {
			ID(a_i),
			ID(b_i),
			ID(c_i),
			ID(z_o),
		};

		// Source DSP cell type (half-block)
		static const IdString m_Dspv1SisdType = ID(dsp_t1_10x9x32_cfg_ports);
		static const IdString m_Dspv2SisdType = ID(dspv2_16x9x32_cfg_ports);

		// Target DSP cell types (full-block)
		static const IdString m_Dspv1SimdType = ID(dsp_t1_20x18x64_cfg_ports_fracturable);
		static const IdString m_Dspv2SimdType = ID(dspv2_32x18x64_cfg_ports);

		// Parse args
		int dsp_version = 1;
		size_t argidx;
		for (argidx = 1; argidx < a_Args.size(); argidx++) {
			if (a_Args[argidx] == "-dspv2") {
				dsp_version = 2;
				continue;
			}
			break;
		}
		extra_args(a_Args, argidx, a_Design);

		log_assert(dsp_version < 3);
		log_assert(dsp_version > 0);
		const auto& cfg_ports = (dsp_version == 1) ? m_Dspv1CfgPorts : m_Dspv2CfgPorts;
		const auto& cfg_params = (dsp_version == 1) ? m_Dspv1CfgParams : m_Dspv2CfgParams;
		const auto& data_ports = (dsp_version == 1) ? m_Dspv1DataPorts : m_Dspv2DataPorts;
		auto half_dsp = (dsp_version == 1) ? m_Dspv1SisdType : m_Dspv2SisdType;
		auto full_dsp = (dsp_version == 1) ? m_Dspv1SimdType : m_Dspv2SimdType;

		int cellsMerged = 0;
		// Process modules
		for (auto module : a_Design->selected_modules()) {
			// Setup the SigMap
			sigmap.set(module);

			// Assemble DSP cell groups
			dict<DspConfig, std::vector<RTLIL::Cell *>> groups;
			for (auto cell : module->selected_cells()) {
				// Check if this is a DSP cell we are looking for (type starts with m_SisdDspType)
				if (cell->type != half_dsp)
					continue;

				// Skip if it has the (* keep *) attribute set
				if (cell->has_keep_attr()) {
					log_debug("skip %s because it's marked keep\n", log_id(cell));
					continue;
				}

				// Skip if it has cascading
				if (is_cascade(cell)) {
					log_debug("skip %s because it's cascading\n", log_id(cell));
					continue;
				}

				// Add to a group
				const auto key = getDspConfig(cell, cfg_ports, cfg_params);
				groups[key].push_back(cell);
			}

			log_debug("Checking %zu detected mode-equivalent DSP cell classes\n", groups.size());
			std::vector<Cell *> cellsToRemove;
			// Map cell pairs to the target DSP SIMD cell
			for (const auto &it : groups) {
				const auto &group = it.second;
				const auto &config = it.first;
				log_debug("Checking %zu half-blocks\n", group.size());
				// Ensure an even number
				size_t count = group.size();
				if (count & 1)
					count--;

				// Map SIMD pairs
				for (size_t i = 0; i < count; i += 2) {
					Cell *dsp_a = group[i];
					Cell *dsp_b = group[i + 1];

					// Create the new cell
					Cell *simd = module->addCell(NEW_ID, full_dsp);

					log(" SIMD: %s (%s) + %s (%s) => %s (%s)\n", log_id(dsp_a), log_id(dsp_a->type),
						log_id(dsp_b), log_id(dsp_b->type), log_id(simd), log_id(simd->type));

					// Check if the target cell is known (important to know
					// its port widths)
					if (!simd->known())
						log_error(" The target cell type '%s' is not known!", log_id(simd->type));
					// Connect common ports

					for (auto port : cfg_ports) {
						if (config.connections.count(port))
							simd->setPort(port, config.connections.at(port));
					}
					for (auto param : cfg_params) {
						if (config.parameters.count(param))
							simd->setParam(param, config.parameters.at(param));
					}

					// Connect data ports
					for (auto port : data_ports) {
						size_t width;
						bool isOutput;

						std::tie(width, isOutput) = getPortInfo(simd, port);
						if (!width)
							log_error("Can't determine portinfo for %s\n", log_id(port));

						auto getConnection = [&](const RTLIL::Cell *cell) {
							RTLIL::SigSpec sigspec;
							if (cell->hasPort(port)) {
								const auto &sig = cell->getPort(port);
								sigspec.append(sig);
							}

							int padding = width / 2 - sigspec.size();
							log_assert(padding >= 0);

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
						simd->setPort(port, sigspec);
					}

					// Enable the fractured mode
					if (dsp_version == 1)
						simd->setPort(ID(f_mode_i), State::S1);
					else
						simd->setParam(ID(FRAC_MODE), State::S1);

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
			cellsMerged += cellsToRemove.size();
			// Remove old cells
			for (auto cell : cellsToRemove)
				module->remove(cell);
		}
		log("Merged %d half-block cells\n", cellsMerged);
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
	DspConfig getDspConfig(RTLIL::Cell *a_Cell, const std::vector<IdString> &dspCfgPorts, const std::vector<IdString> &dspCfgParams)
	{
		DspConfig config;

		for (auto port : dspCfgPorts) {
			// Port unconnected
			if (!a_Cell->hasPort(port))
				continue;

			config.connections[port] = sigmap(a_Cell->getPort(port));
		}
		for (auto param : dspCfgParams) {
			// Param unset?
			if (!a_Cell->hasParam(param))
				continue;

			config.parameters[param] = a_Cell->getParam(param);
		}

		return config;
	}
} QlDspSimdPass;

PRIVATE_NAMESPACE_END
