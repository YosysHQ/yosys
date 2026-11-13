#ifndef NEWCELLTYPES_H
#define NEWCELLTYPES_H

#include "kernel/rtlil.h"
#include "kernel/yosys.h"

YOSYS_NAMESPACE_BEGIN

/**
 * This API is unstable.
 * It may change or be removed in future versions and break dependent code.
 */

namespace StaticCellTypes {

// Given by last internal cell type IdString constids.inc, compilation error if too low
constexpr int MAX_CELLS = 300;
// Currently given by _MUX16_, compilation error if too low
constexpr int MAX_PORTS = 20;
struct CellTableBuilder {
	struct PortList {
		std::array<RTLIL::IdString, MAX_PORTS> ports{};
		size_t count = 0;
		constexpr PortList() = default;
		constexpr PortList(std::initializer_list<RTLIL::IdString> init) {
			for (auto p : init) {
				ports[count++] = p;
			}
		}
		constexpr auto begin() const { return ports.begin(); }
		constexpr auto end() const { return ports.begin() + count; }
		constexpr bool contains(RTLIL::IdString port) const {
			for (size_t i = 0; i < count; i++) {
				if (port == ports[i])
					return true;
			}

			return false;
		}
		constexpr size_t size() const { return count; }
	};
	struct Features {
		bool is_internal = true;
		bool is_evaluable = false;
		bool is_x_aware = false;
		bool is_x_output = false;
		bool is_combinatorial = false;
		bool is_stateless = false;
		bool is_synthesizable = false;
		bool is_stdcell = false;
		bool is_ff = false;
		bool is_mem = false;
		bool is_clocked = false;
		bool is_tristate = false;
		bool has_side_effect = false;
		bool is_nondeterministic = false;
		bool is_formal = false;
		bool is_meta_info = false;
	};
	struct CellInfo {
		RTLIL::IdString type;
		PortList inputs, outputs;
		Features features;
	};
	std::array<CellInfo, MAX_CELLS> cells{};
	size_t count = 0;

	constexpr void setup_type(RTLIL::IdString type, std::initializer_list<RTLIL::IdString> inputs, std::initializer_list<RTLIL::IdString> outputs, const Features& features) {
		Features features_copy = features;
		features_copy.is_internal = true;
		cells[count++] = {type, PortList(inputs), PortList(outputs), features_copy};

	}

	// Setup combinatorial cell type which is synthesizable and evaluable (by default)
	constexpr void setup_comb_type(RTLIL::IdString type, std::initializer_list<RTLIL::IdString> inputs, std::initializer_list<RTLIL::IdString> outputs,
			bool is_evaluable = true, bool is_stdcell = false, bool is_tristate = false,
			bool is_x_aware = false, bool is_x_output = false)
	{
		Features features {};
		features.is_combinatorial = true;
		features.is_stateless = true;
		features.is_evaluable = is_evaluable; // not true for $tribuf, why isn't it valid? are z bits not valid from eval?
		features.is_synthesizable = true;
		features.is_stdcell = is_stdcell;
		features.is_tristate = is_tristate;
		features.is_x_aware = is_x_aware;
		features.is_x_output = is_x_output;
		setup_type(type, inputs, outputs, features);
	}

	// Setup builtin ff cell type which is synthesizable
	constexpr void setup_ff_type(RTLIL::IdString type, std::initializer_list<RTLIL::IdString> inputs, std::initializer_list<RTLIL::IdString> outputs,
		bool is_stdcell = false)
	{
		Features features {};
		features.is_synthesizable = true;
		features.is_ff = true;
		features.is_clocked = true;
		features.is_stdcell = is_stdcell;

		setup_type(type, inputs, outputs, features);
	}

	constexpr void setup_latch_type(RTLIL::IdString type, std::initializer_list<RTLIL::IdString> inputs, std::initializer_list<RTLIL::IdString> outputs,
		bool is_stdcell = false)
	{
		Features features {};
		features.is_synthesizable = true;
		features.is_ff = true;
		features.is_clocked = false;
		features.is_stdcell = is_stdcell;

		setup_type(type, inputs, outputs, features);
	}

	// Setup builtin mem cell type which is synthesizable
	constexpr void setup_mem_type(RTLIL::IdString type, std::initializer_list<RTLIL::IdString> inputs, std::initializer_list<RTLIL::IdString> outputs, bool is_clocked = true)
	{
		Features features {};
		features.is_synthesizable = true;
		features.is_mem = true;
		features.is_clocked = is_clocked;

		setup_type(type, inputs, outputs, features);
	}

	// Setup formal cell type which may be combinatorial, and may have effects
	constexpr void setup_formal_type(RTLIL::IdString type, std::initializer_list<RTLIL::IdString> inputs, std::initializer_list<RTLIL::IdString> outputs,
			bool has_side_effect = false, bool is_nondeterministic = false, bool is_stateless = true)
	{
		Features features {};
		features.is_formal = true;
		features.is_stateless = is_stateless;
		features.has_side_effect = has_side_effect; // assert
		features.is_nondeterministic = is_nondeterministic; // anyseq
		setup_type(type, inputs, outputs, features);
	}

	// Setup cell type which has effects, and may be formal
	constexpr void setup_effects_type(RTLIL::IdString type, std::initializer_list<RTLIL::IdString> inputs, std::initializer_list<RTLIL::IdString> outputs,
			bool is_formal = false)
	{
		Features features {};
		features.is_formal = is_formal;
		features.has_side_effect = true;
		features.is_stateless = true;
		setup_type(type, inputs, outputs, features);
	}

	// Setup meta-info cell type
	constexpr void setup_metainfo_type(RTLIL::IdString type, std::initializer_list<RTLIL::IdString> inputs, std::initializer_list<RTLIL::IdString> outputs)
	{
		Features features {};
		features.is_meta_info = true;
		features.is_stateless = true;
		setup_type(type, inputs, outputs, features);
	}

	constexpr void setup_internals_other()
	{
		Features features {};
		// synthesizable
		setup_comb_type(ID($tribuf), {ID::A, ID::EN}, {ID::Y}, false, false, true);

		// is this evaluable
		features = {};
		features.is_evaluable = false;
		features.is_stateless = true;
		setup_type(ID($barrier), {ID::A}, {ID::Y}, features);

		// has_side_effect, and !is_nondeterministic;
		setup_formal_type(ID($assert), {ID::A, ID::EN}, {}, true, false);
		setup_formal_type(ID($assume), {ID::A, ID::EN}, {}, true, false);
		setup_formal_type(ID($live),   {ID::A, ID::EN}, {}, true, false);
		setup_formal_type(ID($fair),   {ID::A, ID::EN}, {}, true, false);
		setup_formal_type(ID($cover),  {ID::A, ID::EN}, {}, true, false);

		// !has_side_effect, and !is_nondeterministic;
		setup_formal_type(ID($equiv), {ID::A, ID::B}, {ID::Y}, false, false);

		// !has_side_effect, and !is_nondeterministic & !is_stateless;
		setup_formal_type(ID($initstate), {}, {ID::Y}, false, false, false);

		// !has_side_effect, and is_nondeterministic;
		setup_formal_type(ID($anyconst), {}, {ID::Y}, false, true);
		setup_formal_type(ID($anyseq), {}, {ID::Y}, false, true);
		setup_formal_type(ID($allconst), {}, {ID::Y}, false, true);
		setup_formal_type(ID($allseq), {}, {ID::Y}, false, true);

		// !has_side_effect, and is_nondeterministic, & !is_stateless;
		setup_formal_type(ID($anyinit), {ID::D}, {ID::Q}, false, true, false);

		// combinatorial
		features = {};
		features.is_stateless = true;
		setup_type(ID($specify2), {ID::EN, ID::SRC, ID::DST}, {}, features);
		setup_type(ID($specify3), {ID::EN, ID::SRC, ID::DST, ID::DAT}, {}, features);
		setup_type(ID($specrule), {ID::SRC_EN, ID::DST_EN, ID::SRC, ID::DST}, {}, features);

		// !is_formal
		setup_effects_type(ID($print), {ID::EN, ID::ARGS, ID::TRG}, {});
		setup_effects_type(ID($check), {ID::A, ID::EN, ID::ARGS, ID::TRG}, {});

		setup_formal_type(ID($set_tag), {ID::A, ID::SET, ID::CLR}, {ID::Y});
		setup_formal_type(ID($get_tag), {ID::A}, {ID::Y});
		setup_formal_type(ID($overwrite_tag), {ID::A, ID::SET, ID::CLR}, {});
		setup_formal_type(ID($original_tag), {ID::A}, {ID::Y});
		setup_formal_type(ID($future_ff), {ID::A}, {ID::Y});

		// meta-info
		setup_metainfo_type(ID($scopeinfo), {}, {});

		// temporary helper cells
		features = {};
		features.is_stateless = true;
		setup_type(ID($input_port), {}, {ID::Y}, features);
		setup_type(ID($connect), {ID::A, ID::B}, {}, features);
	}
	constexpr void setup_internals_eval()
	{
		std::initializer_list<RTLIL::IdString> unary_ops = {
			ID($not), ID($pos), ID($buf), ID($neg),
			ID($reduce_and), ID($reduce_or), ID($reduce_xor), ID($reduce_xnor), ID($reduce_bool),
			ID($logic_not), ID($slice), ID($lut), ID($sop)
		};

		std::initializer_list<RTLIL::IdString> binary_ops = {
			ID($and), ID($or), ID($xor), ID($xnor),
			ID($shl), ID($shr), ID($sshl), ID($sshr), ID($shift),
			ID($lt), ID($le), ID($eq), ID($ne), ID($ge), ID($gt),
			ID($add), ID($sub), ID($mul), ID($divfloor), ID($modfloor), ID($pow),
			ID($logic_and), ID($logic_or), ID($concat), ID($macc),
		};

		std::initializer_list<RTLIL::IdString> binary_ops_x_aware = {
			ID($eqx), ID($nex), ID($bweqx)
		};

		std::initializer_list<RTLIL::IdString> binary_ops_x_out = {
			ID($shiftx), ID($div), ID($mod),
		};

		for (auto type : unary_ops)
			setup_comb_type(type, {ID::A}, {ID::Y});

		for (auto type : binary_ops)
			setup_comb_type(type, {ID::A, ID::B}, {ID::Y});

		for (auto type : binary_ops_x_aware)
			setup_comb_type(type, {ID::A, ID::B}, {ID::Y}, true, false, false, true);

		for (auto type : binary_ops_x_out)
			setup_comb_type(type, {ID::A, ID::B}, {ID::Y}, true, false, false, false, true);

		for (auto type : {ID($mux), ID($bwmux)})
			setup_comb_type(type, {ID::A, ID::B, ID::S}, {ID::Y});

		setup_comb_type(ID($pmux), {ID::A, ID::B, ID::S}, {ID::Y}, true, false, false, false, true);

		for (auto type : {ID($bmux), ID($demux)})
			setup_comb_type(type, {ID::A, ID::S}, {ID::Y});

		setup_comb_type(ID($lcu), {ID::P, ID::G, ID::CI}, {ID::CO});
		setup_comb_type(ID($alu), {ID::A, ID::B, ID::CI, ID::BI}, {ID::X, ID::Y, ID::CO});
		setup_comb_type(ID($macc_v2), {ID::A, ID::B, ID::C}, {ID::Y});
		setup_comb_type(ID($fa), {ID::A, ID::B, ID::C}, {ID::X, ID::Y});
	}
	constexpr void setup_internals_ff()
	{
		setup_ff_type(ID($sr), {ID::SET, ID::CLR}, {ID::Q});
		setup_ff_type(ID($ff), {ID::D}, {ID::Q});
		setup_ff_type(ID($dff), {ID::CLK, ID::D}, {ID::Q});
		setup_ff_type(ID($dffe), {ID::CLK, ID::EN, ID::D}, {ID::Q});
		setup_ff_type(ID($dffsr), {ID::CLK, ID::SET, ID::CLR, ID::D}, {ID::Q});
		setup_ff_type(ID($dffsre), {ID::CLK, ID::SET, ID::CLR, ID::D, ID::EN}, {ID::Q});
		setup_ff_type(ID($adff), {ID::CLK, ID::ARST, ID::D}, {ID::Q});
		setup_ff_type(ID($adffe), {ID::CLK, ID::ARST, ID::D, ID::EN}, {ID::Q});
		setup_ff_type(ID($aldff), {ID::CLK, ID::ALOAD, ID::AD, ID::D}, {ID::Q});
		setup_ff_type(ID($aldffe), {ID::CLK, ID::ALOAD, ID::AD, ID::D, ID::EN}, {ID::Q});
		setup_ff_type(ID($sdff), {ID::CLK, ID::SRST, ID::D}, {ID::Q});
		setup_ff_type(ID($sdffe), {ID::CLK, ID::SRST, ID::D, ID::EN}, {ID::Q});
		setup_ff_type(ID($sdffce), {ID::CLK, ID::SRST, ID::D, ID::EN}, {ID::Q});
		setup_latch_type(ID($dlatch), {ID::EN, ID::D}, {ID::Q}, false);
		setup_latch_type(ID($adlatch), {ID::EN, ID::D, ID::ARST}, {ID::Q});
		setup_latch_type(ID($dlatchsr), {ID::EN, ID::SET, ID::CLR, ID::D}, {ID::Q});
	}
	constexpr void setup_internals_mem_noff()
	{
		setup_mem_type(ID($memrd), {ID::CLK, ID::EN, ID::ADDR}, {ID::DATA});
		setup_mem_type(ID($memrd_v2), {ID::CLK, ID::EN, ID::ARST, ID::SRST, ID::ADDR}, {ID::DATA});
		setup_mem_type(ID($memwr), {ID::CLK, ID::EN, ID::ADDR, ID::DATA}, {});
		setup_mem_type(ID($memwr_v2), {ID::CLK, ID::EN, ID::ADDR, ID::DATA}, {});
		setup_mem_type(ID($meminit), {ID::ADDR, ID::DATA}, {}, false);
		setup_mem_type(ID($meminit_v2), {ID::ADDR, ID::DATA, ID::EN}, {}, false);
		setup_mem_type(ID($mem), {ID::RD_CLK, ID::RD_EN, ID::RD_ADDR, ID::WR_CLK, ID::WR_EN, ID::WR_ADDR, ID::WR_DATA}, {ID::RD_DATA});
		setup_mem_type(ID($mem_v2), {ID::RD_CLK, ID::RD_EN, ID::RD_ARST, ID::RD_SRST, ID::RD_ADDR, ID::WR_CLK, ID::WR_EN, ID::WR_ADDR, ID::WR_DATA}, {ID::RD_DATA});

		// What?
		Features features {};
		features.is_clocked = true;
		setup_type(ID($fsm), {ID::CLK, ID::ARST, ID::CTRL_IN}, {ID::CTRL_OUT}, features);
	}
	constexpr void setup_stdcells_tristate()
	{
		// !eval, stdcell, tri
		setup_comb_type(ID($_TBUF_), {ID::A, ID::E}, {ID::Y}, false, true, true);
	}

	constexpr void setup_stdcells_eval()
	{
		// eval, stdcell, !tri
		setup_comb_type(ID($_BUF_), {ID::A}, {ID::Y}, true, true, false);
		setup_comb_type(ID($_NOT_), {ID::A}, {ID::Y}, true, true, false);
		setup_comb_type(ID($_AND_), {ID::A, ID::B}, {ID::Y}, true, true, false);
		setup_comb_type(ID($_NAND_), {ID::A, ID::B}, {ID::Y}, true, true, false);
		setup_comb_type(ID($_OR_),  {ID::A, ID::B}, {ID::Y}, true, true, false);
		setup_comb_type(ID($_NOR_),  {ID::A, ID::B}, {ID::Y}, true, true, false);
		setup_comb_type(ID($_XOR_), {ID::A, ID::B}, {ID::Y}, true, true, false);
		setup_comb_type(ID($_XNOR_), {ID::A, ID::B}, {ID::Y}, true, true, false);
		setup_comb_type(ID($_ANDNOT_), {ID::A, ID::B}, {ID::Y}, true, true, false);
		setup_comb_type(ID($_ORNOT_), {ID::A, ID::B}, {ID::Y}, true, true, false);
		setup_comb_type(ID($_MUX_), {ID::A, ID::B, ID::S}, {ID::Y}, true, true, false);
		setup_comb_type(ID($_NMUX_), {ID::A, ID::B, ID::S}, {ID::Y}, true, true, false);
		setup_comb_type(ID($_MUX4_), {ID::A, ID::B, ID::C, ID::D, ID::S, ID::T}, {ID::Y}, true, true, false);
		setup_comb_type(ID($_MUX8_), {ID::A, ID::B, ID::C, ID::D, ID::E, ID::F, ID::G, ID::H, ID::S, ID::T, ID::U}, {ID::Y}, true, true, false);
		setup_comb_type(ID($_MUX16_), {ID::A, ID::B, ID::C, ID::D, ID::E, ID::F, ID::G, ID::H, ID::I, ID::J, ID::K, ID::L, ID::M, ID::N, ID::O, ID::P, ID::S, ID::T, ID::U, ID::V}, {ID::Y}, true, true, false);
		setup_comb_type(ID($_AOI3_), {ID::A, ID::B, ID::C}, {ID::Y}, true, true, false);
		setup_comb_type(ID($_OAI3_), {ID::A, ID::B, ID::C}, {ID::Y}, true, true, false);
		setup_comb_type(ID($_AOI4_), {ID::A, ID::B, ID::C, ID::D}, {ID::Y}, true, true, false);
		setup_comb_type(ID($_OAI4_), {ID::A, ID::B, ID::C, ID::D}, {ID::Y}, true, true, false);
	}

	constexpr void setup_stdcells_ff() {

		std::initializer_list<RTLIL::IdString> sr = {
			ID($_SR_NN_), ID($_SR_NP_), ID($_SR_PN_), ID($_SR_PP_)
		};
		for (auto type : sr) {
			setup_ff_type(type, {ID::S, ID::R}, {ID::Q}, true);
		}

		setup_ff_type(ID($_FF_), {ID::D}, {ID::Q}, true);

		setup_ff_type(ID($_DFF_N_), {ID::C, ID::D}, {ID::Q}, true);
		setup_ff_type(ID($_DFF_P_), {ID::C, ID::D}, {ID::Q}, true);

		std::initializer_list<RTLIL::IdString> dffe = {
			ID($_DFFE_NN_), ID($_DFFE_NP_), ID($_DFFE_PN_), ID($_DFFE_PP_)
		};
		for (auto type : dffe) {
			setup_ff_type(type, {ID::C, ID::D, ID::E}, {ID::Q}, true);
		}

		std::initializer_list<RTLIL::IdString> dff = {
			ID($_DFF_NN0_), ID($_DFF_NN1_), ID($_DFF_NP0_), ID($_DFF_NP1_),
			ID($_DFF_PN0_), ID($_DFF_PN1_), ID($_DFF_PP0_), ID($_DFF_PP1_)
		};
		for (auto type : dff) {
			setup_ff_type(type, {ID::C, ID::R, ID::D}, {ID::Q}, true);
		}

		std::initializer_list<RTLIL::IdString> dffe_reset = {
			ID($_DFFE_NN0N_), ID($_DFFE_NN0P_), ID($_DFFE_NN1N_), ID($_DFFE_NN1P_),
			ID($_DFFE_NP0N_), ID($_DFFE_NP0P_), ID($_DFFE_NP1N_), ID($_DFFE_NP1P_),
			ID($_DFFE_PN0N_), ID($_DFFE_PN0P_), ID($_DFFE_PN1N_), ID($_DFFE_PN1P_),
			ID($_DFFE_PP0N_), ID($_DFFE_PP0P_), ID($_DFFE_PP1N_), ID($_DFFE_PP1P_)
		};
		for (auto type : dffe_reset) {
			setup_ff_type(type, {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, true);
		}

		std::initializer_list<RTLIL::IdString> aldff = {
			ID($_ALDFF_NN_), ID($_ALDFF_NP_), ID($_ALDFF_PN_), ID($_ALDFF_PP_)
		};
		for (auto type : aldff) {
			setup_ff_type(type, {ID::C, ID::L, ID::AD, ID::D}, {ID::Q}, true);
		}

		std::initializer_list<RTLIL::IdString> aldffe = {
			ID($_ALDFFE_NNN_), ID($_ALDFFE_NNP_), ID($_ALDFFE_NPN_), ID($_ALDFFE_NPP_),
			ID($_ALDFFE_PNN_), ID($_ALDFFE_PNP_), ID($_ALDFFE_PPN_), ID($_ALDFFE_PPP_)
		};
		for (auto type : aldffe) {
			setup_ff_type(type, {ID::C, ID::L, ID::AD, ID::D, ID::E}, {ID::Q}, true);
		}

		std::initializer_list<RTLIL::IdString> dffsr = {
			ID($_DFFSR_NNN_), ID($_DFFSR_NNP_), ID($_DFFSR_NPN_), ID($_DFFSR_NPP_),
			ID($_DFFSR_PNN_), ID($_DFFSR_PNP_), ID($_DFFSR_PPN_), ID($_DFFSR_PPP_)
		};
		for (auto type : dffsr) {
			setup_ff_type(type, {ID::C, ID::S, ID::R, ID::D}, {ID::Q}, true);
		}

		std::initializer_list<RTLIL::IdString> dffsre = {
			ID($_DFFSRE_NNNN_), ID($_DFFSRE_NNNP_), ID($_DFFSRE_NNPN_), ID($_DFFSRE_NNPP_),
			ID($_DFFSRE_NPNN_), ID($_DFFSRE_NPNP_), ID($_DFFSRE_NPPN_), ID($_DFFSRE_NPPP_),
			ID($_DFFSRE_PNNN_), ID($_DFFSRE_PNNP_), ID($_DFFSRE_PNPN_), ID($_DFFSRE_PNPP_),
			ID($_DFFSRE_PPNN_), ID($_DFFSRE_PPNP_), ID($_DFFSRE_PPPN_), ID($_DFFSRE_PPPP_)
		};
		for (auto type : dffsre) {
			setup_ff_type(type, {ID::C, ID::S, ID::R, ID::D, ID::E}, {ID::Q}, true);
		}

		std::initializer_list<RTLIL::IdString> sdff = {
			ID($_SDFF_NN0_), ID($_SDFF_NN1_), ID($_SDFF_NP0_), ID($_SDFF_NP1_),
			ID($_SDFF_PN0_), ID($_SDFF_PN1_), ID($_SDFF_PP0_), ID($_SDFF_PP1_)
		};
		for (auto type : sdff) {
			setup_ff_type(type, {ID::C, ID::R, ID::D}, {ID::Q}, true);
		}

		std::initializer_list<RTLIL::IdString> sdffe = {
			ID($_SDFFE_NN0N_), ID($_SDFFE_NN0P_), ID($_SDFFE_NN1N_), ID($_SDFFE_NN1P_),
			ID($_SDFFE_NP0N_), ID($_SDFFE_NP0P_), ID($_SDFFE_NP1N_), ID($_SDFFE_NP1P_),
			ID($_SDFFE_PN0N_), ID($_SDFFE_PN0P_), ID($_SDFFE_PN1N_), ID($_SDFFE_PN1P_),
			ID($_SDFFE_PP0N_), ID($_SDFFE_PP0P_), ID($_SDFFE_PP1N_), ID($_SDFFE_PP1P_)
		};
		for (auto type : sdffe) {
			setup_ff_type(type, {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, true);
		}

		std::initializer_list<RTLIL::IdString> sdffce = {
			ID($_SDFFCE_NN0N_), ID($_SDFFCE_NN0P_), ID($_SDFFCE_NN1N_), ID($_SDFFCE_NN1P_),
			ID($_SDFFCE_NP0N_), ID($_SDFFCE_NP0P_), ID($_SDFFCE_NP1N_), ID($_SDFFCE_NP1P_),
			ID($_SDFFCE_PN0N_), ID($_SDFFCE_PN0P_), ID($_SDFFCE_PN1N_), ID($_SDFFCE_PN1P_),
			ID($_SDFFCE_PP0N_), ID($_SDFFCE_PP0P_), ID($_SDFFCE_PP1N_), ID($_SDFFCE_PP1P_)
		};
		for (auto type : sdffce) {
			setup_ff_type(type, {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, true);
		}

		std::initializer_list<RTLIL::IdString> dlatch = {
			ID($_DLATCH_N_), ID($_DLATCH_P_)
		};
		for (auto type : dlatch) {
			setup_ff_type(type, {ID::E, ID::D}, {ID::Q}, true);
		}

		std::initializer_list<RTLIL::IdString> dlatch_reset = {
			ID($_DLATCH_NN0_), ID($_DLATCH_NN1_), ID($_DLATCH_NP0_), ID($_DLATCH_NP1_),
			ID($_DLATCH_PN0_), ID($_DLATCH_PN1_), ID($_DLATCH_PP0_), ID($_DLATCH_PP1_)
		};
		for (auto type : dlatch_reset) {
			setup_ff_type(type, {ID::E, ID::R, ID::D}, {ID::Q}, true);
		}

		std::initializer_list<RTLIL::IdString> dlatchsr = {
			ID($_DLATCHSR_NNN_), ID($_DLATCHSR_NNP_), ID($_DLATCHSR_NPN_), ID($_DLATCHSR_NPP_),
			ID($_DLATCHSR_PNN_), ID($_DLATCHSR_PNP_), ID($_DLATCHSR_PPN_), ID($_DLATCHSR_PPP_)
		};
		for (auto type : dlatchsr) {
			setup_ff_type(type, {ID::E, ID::S, ID::R, ID::D}, {ID::Q}, true);
		}
	}
	constexpr CellTableBuilder() {
		setup_internals_other();
		setup_internals_eval();
		setup_internals_ff();
		setup_internals_mem_noff();
		setup_stdcells_tristate();
		setup_stdcells_eval();
		setup_stdcells_ff();
	}

};

constexpr CellTableBuilder builder {};

struct PortInfo {
	struct PortLists {
		std::array<CellTableBuilder::PortList, MAX_CELLS> data{};
		constexpr CellTableBuilder::PortList operator()(IdString type) const {
			return data[type.raw()];
		}
		constexpr CellTableBuilder::PortList& operator[](size_t idx) {
			return data[idx];
		}
		constexpr size_t size() const { return data.size(); }
	};
	PortLists inputs {};
	PortLists outputs {};
	constexpr PortInfo() {
		for (size_t i = 0; i < builder.count; ++i) {
			auto& cell = builder.cells[i];
			size_t idx = cell.type.raw();
			inputs[idx] = cell.inputs;
			outputs[idx] = cell.outputs;
		}
	}
};

struct Categories {
	struct Category {
		std::array<bool, MAX_CELLS> data{};
		constexpr bool operator()(IdString type) const {
			size_t idx = type.raw();
			if (idx >= MAX_CELLS)
				return false;
			return data[idx];
		}
		constexpr bool operator[](size_t idx) {
			return data[idx];
		}
		constexpr void set_id(IdString type, bool val = true) {
			size_t idx = type.raw();
			if (idx >= MAX_CELLS) {
				if (std::is_constant_evaluated())
					throw "cell type index out of range";
				log_abort();
			}
			data[idx] = val;
		}
		constexpr void set(size_t idx, bool val = true) {
			data[idx] = val;
		}
		constexpr size_t size() const { return data.size(); }
	};
	Category empty {};
	Category is_internal {};
	Category is_known {};
	Category is_evaluable {};
	Category is_x_aware {};
	Category is_x_output {};
	Category is_combinatorial {};
	Category is_stateless {};
	Category is_clocked {};
	Category is_synthesizable {};
	Category is_stdcell {};
	Category is_ff {};
	Category is_mem {};
	Category is_anyinit {};
	Category is_tristate {};
	Category has_side_effect {};
	Category is_nondeterministic {};
	Category is_formal {};
	Category is_meta_info {};
	constexpr Categories() {
		for (size_t i = 0; i < builder.count; ++i) {
			auto& cell = builder.cells[i];
			size_t idx = cell.type.raw();
			is_known.set(idx);
			is_internal.set(idx, cell.features.is_internal);
			is_evaluable.set(idx, cell.features.is_evaluable);
			is_x_aware.set(idx, cell.features.is_x_aware);
			is_x_output.set(idx, cell.features.is_x_output);
			is_combinatorial.set(idx, cell.features.is_combinatorial);
			is_stateless.set(idx, cell.features.is_stateless);
			is_clocked.set(idx, cell.features.is_clocked);
			is_synthesizable.set(idx, cell.features.is_synthesizable);
			is_stdcell.set(idx, cell.features.is_stdcell);
			is_ff.set(idx, cell.features.is_ff);
			is_mem.set(idx, cell.features.is_mem);
			is_tristate.set(idx, cell.features.is_tristate);
			has_side_effect.set(idx, cell.features.has_side_effect);
			is_nondeterministic.set(idx, cell.features.is_nondeterministic);
			is_formal.set(idx, cell.features.is_formal);
			is_meta_info.set(idx, cell.features.is_meta_info);
		}
	}
	template<typename... Args>
	constexpr static Category join(Args... args) {
		Category c {};
		for (size_t i = 0; i < MAX_CELLS; ++i) {
			c.set(i, ( ... || args[i]));
		}
		return c;
	}
	template<typename... Args>
	constexpr static Category meet(Args... args) {
		Category c {};
		for (size_t i = 0; i < MAX_CELLS; ++i) {
			c.set(i, (... && args[i]));
		}
		return c;
	}
	// Sketchy! Make sure to always meet with only the known universe.
	// In other words, no modus tollens allowed
	constexpr static Category complement(Category arg) {
		Category c {};
		for (size_t i = 0; i < MAX_CELLS; ++i) {
			c.set(i, !arg[i]);
		}
		return c;
	}
	constexpr std::optional<Category> lookup(const std::string &property) const {
		if (property == "empty") {
			return empty;
		} else
		if (property == "is_internal") {
			return is_internal;
		} else
		if (property == "is_known") {
			return is_known;
		} else
		if (property == "is_evaluable") {
			return is_evaluable;
		} else
		if (property == "is_x_aware") {
			return is_x_aware;
		} else
		if (property == "is_x_output") {
			return is_x_output;
		} else
		if (property == "is_combinatorial") {
			return is_combinatorial;
		} else
		if (property == "is_clocked") {
			return is_clocked;
		} else
		if (property == "is_stateless") {
			return is_stateless;
		} else
		if (property == "is_synthesizable") {
			return is_synthesizable;
		} else
		if (property == "is_stdcell") {
			return is_stdcell;
		} else
		if (property == "is_ff") {
			return is_ff;
		} else
		if (property == "is_mem") {
			return is_mem;
		} else
		if (property == "is_tristate") {
			return is_tristate;
		} else
		if (property == "has_side_effect") {
			return has_side_effect;
		} else
		if (property == "is_nondeterministic") {
			return is_nondeterministic;
		} else
		if (property == "is_formal") {
			return is_formal;
		} else
		if (property == "is_meta_info") {
			return is_meta_info;
		} else return std::nullopt;
	}
};

// Pure
static constexpr PortInfo port_info;
static constexpr Categories categories;

// Legacy
namespace Compat {
	static constexpr auto internals_all = Categories::meet(categories.is_known, Categories::complement(categories.is_stdcell));
	static constexpr auto mem_ff = Categories::join(categories.is_ff, categories.is_mem);
	// old setup_internals + setup_stdcells
	static constexpr auto nomem_noff = Categories::meet(categories.is_known, Categories::complement(mem_ff));
	static constexpr auto internals_mem_ff = Categories::meet(internals_all, mem_ff);
	// old setup_internals
	static constexpr auto internals_nomem_noff = Categories::meet(internals_all, nomem_noff);
	// old setup_stdcells
	static constexpr auto stdcells_nomem_noff = Categories::meet(categories.is_stdcell, nomem_noff);
	static constexpr auto stdcells_mem = Categories::meet(categories.is_stdcell, categories.is_mem);
	// old setup_internals_eval
	// static constexpr auto internals_eval = Categories::meet(internals_all, categories.is_evaluable);
};

namespace {
	static_assert(categories.is_clocked(ID($dff)));
	static_assert(categories.is_clocked(ID($memrd)));
	static_assert(!categories.is_clocked(ID($and)));
	static_assert(!categories.is_clocked(ID($dlatch)));
	static_assert((*categories.lookup("is_clocked"))(ID($dff)));
	static_assert(categories.is_stateless(ID($and)));
	static_assert(categories.is_stateless(ID($anyseq)));
	static_assert(!categories.is_stateless(ID($initstate)));
	static_assert(!categories.is_stateless(ID($dff)));
	static_assert(!categories.is_stateless(ID($mem_v2)));
	static_assert(!categories.is_stateless(ID($anyinit)));
	static_assert(categories.lookup("is_stateless")->operator()(ID($and)));
	static_assert(categories.is_evaluable(ID($and)));
	static_assert(!categories.is_ff(ID($and)));
	static_assert(Categories::join(categories.is_evaluable, categories.is_ff)(ID($and)));
	static_assert(Categories::join(categories.is_evaluable, categories.is_ff)(ID($dffsr)));
	static_assert(!Categories::join(categories.is_evaluable, categories.is_ff)(ID($anyinit)));
	static_assert(categories.has_side_effect(ID($print)));
	static_assert(!categories.has_side_effect(ID($and)));
	static_assert(categories.is_nondeterministic(ID($anyinit)));
	static_assert(!categories.is_nondeterministic(ID($initstate)));
	static_assert(categories.is_formal(ID($initstate)));
	static_assert(!categories.is_formal(ID($and)));
	static_assert(categories.is_x_aware(ID($eqx)));
	static_assert(!categories.is_x_aware(ID($eq)));
	static_assert(categories.is_x_output(ID($div)));
	static_assert(!categories.is_x_output(ID($shift)));
}

};

struct NewCellType {
	RTLIL::IdString type;
	pool<RTLIL::IdString> inputs, outputs;
	bool is_evaluable;
	bool is_combinatorial;
	bool is_synthesizable;
};

struct NewCellTypes {
	StaticCellTypes::Categories::Category static_cell_types = StaticCellTypes::categories.empty;
	dict<IdString, NewCellType> custom_cell_types {};

	NewCellTypes() {
		static_cell_types = StaticCellTypes::categories.empty;
	}

	NewCellTypes(RTLIL::Design *design) {
		static_cell_types = StaticCellTypes::categories.empty;
		setup(design);
	}
	void setup(RTLIL::Design *design = NULL) {
		if (design)
			setup_design(design);
		static_cell_types = StaticCellTypes::categories.is_known;
	}
	void setup_design(RTLIL::Design *design) {
		for (auto module : design->modules())
			setup_module(module);
	}

	void setup_module(RTLIL::Module *module) {
		pool<IdString> inputs, outputs;
		for (auto wire_name : module->ports) {
			RTLIL::Wire *wire = module->wire(wire_name);
			if (wire->port_input)
				inputs.insert(wire->name);
			if (wire->port_output)
				outputs.insert(wire->name);
		}
		setup_type(module->name, inputs, outputs);
	}

	void setup_type(RTLIL::IdString type, const pool<RTLIL::IdString> &inputs, const pool<RTLIL::IdString> &outputs, bool is_evaluable = false, bool is_combinatorial = false, bool is_synthesizable = false) {
		NewCellType ct = {type, inputs, outputs, is_evaluable, is_combinatorial, is_synthesizable};
		custom_cell_types[ct.type] = ct;
	}

	void clear() {
		custom_cell_types.clear();
		static_cell_types = StaticCellTypes::categories.empty;
	}

	bool cell_known(IdString type) const {
		return static_cell_types(type) || custom_cell_types.count(type) != 0;
	}

	bool cell_output(IdString type, IdString port) const
	{
		if (static_cell_types(type) && StaticCellTypes::port_info.outputs(type).contains(port)) {
			return true;
		}
		auto it = custom_cell_types.find(type);
		return it != custom_cell_types.end() && it->second.outputs.count(port) != 0;
	}

	bool cell_input(IdString type, IdString port) const
	{
		if (static_cell_types(type) && StaticCellTypes::port_info.inputs(type).contains(port)) {
			return true;
		}
		auto it = custom_cell_types.find(type);
		return it != custom_cell_types.end() && it->second.inputs.count(port) != 0;
	}

	RTLIL::PortDir cell_port_dir(RTLIL::IdString type, RTLIL::IdString port) const
	{
		bool is_input, is_output;
		if (static_cell_types(type)) {
			is_input = StaticCellTypes::port_info.inputs(type).contains(port);
			is_output = StaticCellTypes::port_info.outputs(type).contains(port);
		} else {
			auto it = custom_cell_types.find(type);
			if (it == custom_cell_types.end())
				return RTLIL::PD_UNKNOWN;
			is_input = it->second.inputs.count(port);
			is_output = it->second.outputs.count(port);
		}
		return RTLIL::PortDir(is_input + is_output * 2);
	}
	bool cell_evaluable(IdString type) const
	{
		return static_cell_types(type) && StaticCellTypes::categories.is_evaluable(type);
	}
};

extern NewCellTypes yosys_celltypes;

YOSYS_NAMESPACE_END

#endif
