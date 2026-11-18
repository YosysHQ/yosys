#include "kernel/newcelltypes.h"

YOSYS_NAMESPACE_BEGIN

namespace StaticCellTypes {

constexpr void CellTableBuilder::setup_type(RTLIL::IdString type, std::initializer_list<RTLIL::IdString> inputs, std::initializer_list<RTLIL::IdString> outputs, const Features& features) {
	Features features_copy = features;
	features_copy.is_mem_noff = features.is_mem;
	features_copy.is_internal = true;
	cells[count++] = {type, PortList(inputs), PortList(outputs), features_copy};
}

constexpr void CellTableBuilder::setup_comb_type(RTLIL::IdString type, std::initializer_list<RTLIL::IdString> inputs, std::initializer_list<RTLIL::IdString> outputs,
	bool is_evaluable, bool is_stdcell, bool is_tristate,
	bool is_x_aware, bool is_x_output)
{
	Features features {};
	features.is_combinatorial = true;
	features.is_evaluable = is_evaluable;
	features.is_synthesizable = true;
	features.is_stdcell = is_stdcell;
	features.is_tristate = is_tristate;
	features.is_x_aware = is_x_aware;
	features.is_x_output = is_x_output;
	setup_type(type, inputs, outputs, features);
}

constexpr void CellTableBuilder::setup_ff_type(RTLIL::IdString type, std::initializer_list<RTLIL::IdString> inputs, std::initializer_list<RTLIL::IdString> outputs,
	bool is_stdcell)
{
	Features features {};
	features.is_stateless = false;
	features.is_synthesizable = true;
	features.is_ff = true;
	features.is_clocked = true;
	features.is_stdcell = is_stdcell;

	setup_type(type, inputs, outputs, features);
}

constexpr void CellTableBuilder::setup_latch_type(RTLIL::IdString type, std::initializer_list<RTLIL::IdString> inputs, std::initializer_list<RTLIL::IdString> outputs,
	bool is_stdcell)
{
	Features features {};
	features.is_stateless = false;
	features.is_synthesizable = true;
	features.is_ff = true;
	features.is_clocked = false;
	features.is_stdcell = is_stdcell;

	setup_type(type, inputs, outputs, features);
}

constexpr void CellTableBuilder::setup_mem_type(RTLIL::IdString type, std::initializer_list<RTLIL::IdString> inputs, std::initializer_list<RTLIL::IdString> outputs, bool is_clocked)
{
	Features features {};
	features.is_stateless = false;
	features.is_synthesizable = true;
	features.is_mem = true;
	features.is_clocked = is_clocked;

	setup_type(type, inputs, outputs, features);
}

constexpr void CellTableBuilder::setup_formal_type(RTLIL::IdString type, std::initializer_list<RTLIL::IdString> inputs, std::initializer_list<RTLIL::IdString> outputs,
	bool has_side_effect, bool is_nondeterministic, bool is_stateless)
{
	Features features {};
	features.is_formal = true;
	features.is_stateless = is_stateless;
	features.has_side_effect = has_side_effect; // assert
	features.is_nondeterministic = is_nondeterministic; // anyseq
	setup_type(type, inputs, outputs, features);
}

constexpr void CellTableBuilder::setup_effects_type(RTLIL::IdString type, std::initializer_list<RTLIL::IdString> inputs, std::initializer_list<RTLIL::IdString> outputs,
	bool is_formal)
{
	Features features {};
	features.is_formal = is_formal;
	features.has_side_effect = true;
	setup_type(type, inputs, outputs, features);
}

constexpr void CellTableBuilder::setup_metainfo_type(RTLIL::IdString type, std::initializer_list<RTLIL::IdString> inputs, std::initializer_list<RTLIL::IdString> outputs)
{
	Features features {};
	features.is_meta_info = true;
	setup_type(type, inputs, outputs, features);
}

constexpr void CellTableBuilder::setup_internals_other()
{
	Features features {};
	// synthesizable
	setup_comb_type(ID($tribuf), {ID::A, ID::EN}, {ID::Y}, /*is_evaluable=*/ false, /*is_stdcell=*/ false, /*is_tristate=*/ true);

	// is this evaluable
	features = {};
	features.is_evaluable = false;
	setup_type(ID($barrier), {ID::A}, {ID::Y}, features);

	std::initializer_list<RTLIL::IdString> formal_checks = {
		ID($assert), ID($assume), ID($live), ID($fair), ID($cover)
	};
	for (const auto& id : formal_checks)
		setup_formal_type(id, {ID::A, ID::EN}, {},         /*has_side_effect=*/ true,  /*is_nondeterministic=*/ false);
	setup_formal_type(ID($equiv), {ID::A, ID::B}, {ID::Y}, /*has_side_effect=*/ false, /*is_nondeterministic=*/ false);
	setup_formal_type(ID($initstate), {}, {ID::Y},         /*has_side_effect=*/ false, /*is_nondeterministic=*/ false, /*is_stateless=*/ false);

	std::initializer_list<RTLIL::IdString> formal_values = {
		ID($anyconst), ID($anyseq), ID($allconst), ID($allseq)
	};
	for (auto type : formal_values)
		setup_formal_type(type, {}, {ID::Y},          /*has_side_effect=*/ false, /*is_nondeterministic=*/ true);
	setup_formal_type(ID($anyinit), {ID::D}, {ID::Q}, /*has_side_effect=*/ false, /*is_nondeterministic=*/ true, /*is_stateless=*/ false);

	// combinatorial
	features = {};
	setup_type(ID($specify2), {ID::EN, ID::SRC, ID::DST}, {}, features);
	setup_type(ID($specify3), {ID::EN, ID::SRC, ID::DST, ID::DAT}, {}, features);
	setup_type(ID($specrule), {ID::SRC_EN, ID::DST_EN, ID::SRC, ID::DST}, {}, features);

	setup_effects_type(ID($print), {ID::EN, ID::ARGS, ID::TRG}, {});
	setup_effects_type(ID($check), {ID::A, ID::EN, ID::ARGS, ID::TRG}, {});

	setup_formal_type(ID($set_tag), {ID::A, ID::SET, ID::CLR}, {ID::Y});
	setup_formal_type(ID($get_tag), {ID::A}, {ID::Y});
	setup_formal_type(ID($overwrite_tag), {ID::A, ID::SET, ID::CLR}, {});
	std::initializer_list<RTLIL::IdString> formal_passthroughs = {
		ID($original_tag), ID($future_ff)
	};
	for (auto type : formal_passthroughs)
		setup_formal_type(type, {ID::A}, {ID::Y});

	// meta-info
	setup_metainfo_type(ID($scopeinfo), {}, {});

	// temporary helper cells
	features = {};
	setup_type(ID($input_port), {}, {ID::Y}, features);
	setup_type(ID($connect), {ID::A, ID::B}, {}, features);
}

constexpr void CellTableBuilder::setup_internals_eval()
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
		setup_comb_type(type, {ID::A, ID::B}, {ID::Y}, /*is_evaluable=*/ true, /*is_stdcell=*/ false, /*is_tristate=*/ false, /*is_x_aware=*/ true);

	for (auto type : binary_ops_x_out)
		setup_comb_type(type, {ID::A, ID::B}, {ID::Y}, /*is_evaluable=*/ true, /*is_stdcell=*/ false, /*is_tristate=*/ false, /*is_x_aware=*/ false, /*is_x_output=*/ true);

	std::initializer_list<RTLIL::IdString> mux_ops = {
		ID($mux), ID($bwmux)
	};
	for (auto type : mux_ops)
		setup_comb_type(type, {ID::A, ID::B, ID::S}, {ID::Y});

	setup_comb_type(ID($pmux), {ID::A, ID::B, ID::S}, {ID::Y}, /*is_evaluable=*/ true, /*is_stdcell=*/ false, /*is_tristate=*/ false, /*is_x_aware=*/ false, /*is_x_output=*/ true);

	std::initializer_list<RTLIL::IdString> demux_ops = {
		ID($bmux), ID($demux)
	};
	for (auto type : demux_ops)
		setup_comb_type(type, {ID::A, ID::S}, {ID::Y});

	setup_comb_type(ID($lcu), {ID::P, ID::G, ID::CI}, {ID::CO});
	setup_comb_type(ID($alu), {ID::A, ID::B, ID::CI, ID::BI}, {ID::X, ID::Y, ID::CO});
	setup_comb_type(ID($macc_v2), {ID::A, ID::B, ID::C}, {ID::Y});
	setup_comb_type(ID($fa), {ID::A, ID::B, ID::C}, {ID::X, ID::Y});
}

constexpr void CellTableBuilder::setup_internals_ff()
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
	std::initializer_list<RTLIL::IdString> sdff_enable = {
		ID($sdffe), ID($sdffce)
	};
	for (auto type : sdff_enable)
		setup_ff_type(type, {ID::CLK, ID::SRST, ID::D, ID::EN}, {ID::Q});

	setup_latch_type(ID($dlatch), {ID::EN, ID::D}, {ID::Q});
	setup_latch_type(ID($adlatch), {ID::EN, ID::D, ID::ARST}, {ID::Q});
	setup_latch_type(ID($dlatchsr), {ID::EN, ID::SET, ID::CLR, ID::D}, {ID::Q});
}

constexpr void CellTableBuilder::setup_internals_mem_noff()
{
	setup_mem_type(ID($memrd), {ID::CLK, ID::EN, ID::ADDR}, {ID::DATA});
	setup_mem_type(ID($memrd_v2), {ID::CLK, ID::EN, ID::ARST, ID::SRST, ID::ADDR}, {ID::DATA});
	std::initializer_list<RTLIL::IdString> mem_writes = {
		ID($memwr), ID($memwr_v2)
	};
	for (auto type : mem_writes)
		setup_mem_type(type, {ID::CLK, ID::EN, ID::ADDR, ID::DATA}, {});

	setup_mem_type(ID($meminit), {ID::ADDR, ID::DATA}, {},            /*is_clocked=*/ false);
	setup_mem_type(ID($meminit_v2), {ID::ADDR, ID::DATA, ID::EN}, {}, /*is_clocked=*/ false);
	setup_mem_type(ID($mem), {ID::RD_CLK, ID::RD_EN, ID::RD_ADDR, ID::WR_CLK, ID::WR_EN, ID::WR_ADDR, ID::WR_DATA}, {ID::RD_DATA});
	setup_mem_type(ID($mem_v2), {ID::RD_CLK, ID::RD_EN, ID::RD_ARST, ID::RD_SRST, ID::RD_ADDR, ID::WR_CLK, ID::WR_EN, ID::WR_ADDR, ID::WR_DATA}, {ID::RD_DATA});

	// What?
	Features features {};
	features.is_clocked = true;
	features.is_stateless = false;
	setup_type(ID($fsm), {ID::CLK, ID::ARST, ID::CTRL_IN}, {ID::CTRL_OUT}, features);
}

constexpr void CellTableBuilder::setup_stdcells_tristate()
{
	setup_comb_type(ID($_TBUF_), {ID::A, ID::E}, {ID::Y}, /*is_evaluable=*/ false, /*is_stdcell=*/ true, /*is_tristate=*/ true);
}

constexpr void CellTableBuilder::setup_stdcells_eval()
{
	std::initializer_list<RTLIL::IdString> unary_ops = {
		ID($_BUF_), ID($_NOT_)
	};
	for (auto type : unary_ops)
		setup_comb_type(type, {ID::A}, {ID::Y}, /*is_evaluable=*/ true, /*is_stdcell=*/ true, /*is_tristate=*/ false);

	std::initializer_list<RTLIL::IdString> binary_ops = {
		ID($_AND_), ID($_NAND_), ID($_OR_), ID($_NOR_),
		ID($_XOR_), ID($_XNOR_), ID($_ANDNOT_), ID($_ORNOT_)
	};
	for (auto type : binary_ops)
		setup_comb_type(type, {ID::A, ID::B}, {ID::Y}, /*is_evaluable=*/ true, /*is_stdcell=*/ true, /*is_tristate=*/ false);

	std::initializer_list<RTLIL::IdString> mux_ops = {
		ID($_MUX_), ID($_NMUX_)
	};
	for (auto type : mux_ops)
		setup_comb_type(type, {ID::A, ID::B, ID::S}, {ID::Y}, /*is_evaluable=*/ true, /*is_stdcell=*/ true, /*is_tristate=*/ false);

	setup_comb_type(ID($_MUX4_), {ID::A, ID::B, ID::C, ID::D, ID::S, ID::T}, {ID::Y}, /*is_evaluable=*/ false, /*is_stdcell=*/ true, /*is_tristate=*/ false);
	setup_comb_type(ID($_MUX8_), {ID::A, ID::B, ID::C, ID::D, ID::E, ID::F, ID::G, ID::H, ID::S, ID::T, ID::U}, {ID::Y}, /*is_evaluable=*/ false, /*is_stdcell=*/ true, /*is_tristate=*/ false);
	setup_comb_type(ID($_MUX16_), {ID::A, ID::B, ID::C, ID::D, ID::E, ID::F, ID::G, ID::H, ID::I, ID::J, ID::K, ID::L, ID::M, ID::N, ID::O, ID::P, ID::S, ID::T, ID::U, ID::V}, {ID::Y}, /*is_evaluable=*/ false, /*is_stdcell=*/ true, /*is_tristate=*/ false);
	std::initializer_list<RTLIL::IdString> triple_ops = {
		ID($_AOI3_), ID($_OAI3_)
	};
	for (auto type : triple_ops)
		setup_comb_type(type, {ID::A, ID::B, ID::C}, {ID::Y}, /*is_evaluable=*/ true, /*is_stdcell=*/ true, /*is_tristate=*/ false);

	std::initializer_list<RTLIL::IdString> quad_ops = {
		ID($_AOI4_), ID($_OAI4_)
	};
	for (auto type : quad_ops)
		setup_comb_type(type, {ID::A, ID::B, ID::C, ID::D}, {ID::Y}, /*is_evaluable=*/ true, /*is_stdcell=*/ true, /*is_tristate=*/ false);
}

constexpr void CellTableBuilder::setup_stdcells_ff() {

	std::initializer_list<RTLIL::IdString> sr = {
		ID($_SR_NN_), ID($_SR_NP_), ID($_SR_PN_), ID($_SR_PP_)
	};
	for (auto type : sr) {
		setup_ff_type(type, {ID::S, ID::R}, {ID::Q}, /*is_stdcell=*/ true);
	}

	setup_ff_type(ID($_FF_), {ID::D}, {ID::Q}, /*is_stdcell=*/ true);

	std::initializer_list<RTLIL::IdString> dff_no_reset = {
		ID($_DFF_N_), ID($_DFF_P_)
	};
	for (auto type : dff_no_reset)
		setup_ff_type(type, {ID::C, ID::D}, {ID::Q}, /*is_stdcell=*/ true);

	std::initializer_list<RTLIL::IdString> dffe = {
		ID($_DFFE_NN_), ID($_DFFE_NP_), ID($_DFFE_PN_), ID($_DFFE_PP_)
	};
	for (auto type : dffe) {
		setup_ff_type(type, {ID::C, ID::D, ID::E}, {ID::Q}, /*is_stdcell=*/ true);
	}

	std::initializer_list<RTLIL::IdString> dff = {
		ID($_DFF_NN0_), ID($_DFF_NN1_), ID($_DFF_NP0_), ID($_DFF_NP1_),
		ID($_DFF_PN0_), ID($_DFF_PN1_), ID($_DFF_PP0_), ID($_DFF_PP1_)
	};
	for (auto type : dff) {
		setup_ff_type(type, {ID::C, ID::R, ID::D}, {ID::Q}, /*is_stdcell=*/ true);
	}

	std::initializer_list<RTLIL::IdString> dffe_reset = {
		ID($_DFFE_NN0N_), ID($_DFFE_NN0P_), ID($_DFFE_NN1N_), ID($_DFFE_NN1P_),
		ID($_DFFE_NP0N_), ID($_DFFE_NP0P_), ID($_DFFE_NP1N_), ID($_DFFE_NP1P_),
		ID($_DFFE_PN0N_), ID($_DFFE_PN0P_), ID($_DFFE_PN1N_), ID($_DFFE_PN1P_),
		ID($_DFFE_PP0N_), ID($_DFFE_PP0P_), ID($_DFFE_PP1N_), ID($_DFFE_PP1P_)
	};
	for (auto type : dffe_reset) {
		setup_ff_type(type, {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, /*is_stdcell=*/ true);
	}

	std::initializer_list<RTLIL::IdString> aldff = {
		ID($_ALDFF_NN_), ID($_ALDFF_NP_), ID($_ALDFF_PN_), ID($_ALDFF_PP_)
	};
	for (auto type : aldff) {
		setup_ff_type(type, {ID::C, ID::L, ID::AD, ID::D}, {ID::Q}, /*is_stdcell=*/ true);
	}

	std::initializer_list<RTLIL::IdString> aldffe = {
		ID($_ALDFFE_NNN_), ID($_ALDFFE_NNP_), ID($_ALDFFE_NPN_), ID($_ALDFFE_NPP_),
		ID($_ALDFFE_PNN_), ID($_ALDFFE_PNP_), ID($_ALDFFE_PPN_), ID($_ALDFFE_PPP_)
	};
	for (auto type : aldffe) {
		setup_ff_type(type, {ID::C, ID::L, ID::AD, ID::D, ID::E}, {ID::Q}, /*is_stdcell=*/ true);
	}

	std::initializer_list<RTLIL::IdString> dffsr = {
		ID($_DFFSR_NNN_), ID($_DFFSR_NNP_), ID($_DFFSR_NPN_), ID($_DFFSR_NPP_),
		ID($_DFFSR_PNN_), ID($_DFFSR_PNP_), ID($_DFFSR_PPN_), ID($_DFFSR_PPP_)
	};
	for (auto type : dffsr) {
		setup_ff_type(type, {ID::C, ID::S, ID::R, ID::D}, {ID::Q}, /*is_stdcell=*/ true);
	}

	std::initializer_list<RTLIL::IdString> dffsre = {
		ID($_DFFSRE_NNNN_), ID($_DFFSRE_NNNP_), ID($_DFFSRE_NNPN_), ID($_DFFSRE_NNPP_),
		ID($_DFFSRE_NPNN_), ID($_DFFSRE_NPNP_), ID($_DFFSRE_NPPN_), ID($_DFFSRE_NPPP_),
		ID($_DFFSRE_PNNN_), ID($_DFFSRE_PNNP_), ID($_DFFSRE_PNPN_), ID($_DFFSRE_PNPP_),
		ID($_DFFSRE_PPNN_), ID($_DFFSRE_PPNP_), ID($_DFFSRE_PPPN_), ID($_DFFSRE_PPPP_)
	};
	for (auto type : dffsre) {
		setup_ff_type(type, {ID::C, ID::S, ID::R, ID::D, ID::E}, {ID::Q}, /*is_stdcell=*/ true);
	}

	std::initializer_list<RTLIL::IdString> sdff = {
		ID($_SDFF_NN0_), ID($_SDFF_NN1_), ID($_SDFF_NP0_), ID($_SDFF_NP1_),
		ID($_SDFF_PN0_), ID($_SDFF_PN1_), ID($_SDFF_PP0_), ID($_SDFF_PP1_)
	};
	for (auto type : sdff) {
		setup_ff_type(type, {ID::C, ID::R, ID::D}, {ID::Q}, /*is_stdcell=*/ true);
	}

	std::initializer_list<RTLIL::IdString> sdffe = {
		ID($_SDFFE_NN0N_), ID($_SDFFE_NN0P_), ID($_SDFFE_NN1N_), ID($_SDFFE_NN1P_),
		ID($_SDFFE_NP0N_), ID($_SDFFE_NP0P_), ID($_SDFFE_NP1N_), ID($_SDFFE_NP1P_),
		ID($_SDFFE_PN0N_), ID($_SDFFE_PN0P_), ID($_SDFFE_PN1N_), ID($_SDFFE_PN1P_),
		ID($_SDFFE_PP0N_), ID($_SDFFE_PP0P_), ID($_SDFFE_PP1N_), ID($_SDFFE_PP1P_)
	};
	for (auto type : sdffe) {
		setup_ff_type(type, {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, /*is_stdcell=*/ true);
	}

	std::initializer_list<RTLIL::IdString> sdffce = {
		ID($_SDFFCE_NN0N_), ID($_SDFFCE_NN0P_), ID($_SDFFCE_NN1N_), ID($_SDFFCE_NN1P_),
		ID($_SDFFCE_NP0N_), ID($_SDFFCE_NP0P_), ID($_SDFFCE_NP1N_), ID($_SDFFCE_NP1P_),
		ID($_SDFFCE_PN0N_), ID($_SDFFCE_PN0P_), ID($_SDFFCE_PN1N_), ID($_SDFFCE_PN1P_),
		ID($_SDFFCE_PP0N_), ID($_SDFFCE_PP0P_), ID($_SDFFCE_PP1N_), ID($_SDFFCE_PP1P_)
	};
	for (auto type : sdffce) {
		setup_ff_type(type, {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, /*is_stdcell=*/ true);
	}

	std::initializer_list<RTLIL::IdString> dlatch = {
		ID($_DLATCH_N_), ID($_DLATCH_P_)
	};
	for (auto type : dlatch) {
		setup_ff_type(type, {ID::E, ID::D}, {ID::Q}, /*is_stdcell=*/ true);
	}

	std::initializer_list<RTLIL::IdString> dlatch_reset = {
		ID($_DLATCH_NN0_), ID($_DLATCH_NN1_), ID($_DLATCH_NP0_), ID($_DLATCH_NP1_),
		ID($_DLATCH_PN0_), ID($_DLATCH_PN1_), ID($_DLATCH_PP0_), ID($_DLATCH_PP1_)
	};
	for (auto type : dlatch_reset) {
		setup_ff_type(type, {ID::E, ID::R, ID::D}, {ID::Q}, /*is_stdcell=*/ true);
	}

	std::initializer_list<RTLIL::IdString> dlatchsr = {
		ID($_DLATCHSR_NNN_), ID($_DLATCHSR_NNP_), ID($_DLATCHSR_NPN_), ID($_DLATCHSR_NPP_),
		ID($_DLATCHSR_PNN_), ID($_DLATCHSR_PNP_), ID($_DLATCHSR_PPN_), ID($_DLATCHSR_PPP_)
	};
	for (auto type : dlatchsr) {
		setup_ff_type(type, {ID::E, ID::S, ID::R, ID::D}, {ID::Q}, /*is_stdcell=*/ true);
	}
}

constexpr CellTableBuilder::CellTableBuilder() {
	setup_internals_other();
	setup_internals_eval();
	setup_internals_ff();
	setup_internals_mem_noff();
	setup_stdcells_tristate();
	setup_stdcells_eval();
	setup_stdcells_ff();
}

constexpr CellTableBuilder builder {};

constexpr PortInfo::PortInfo() {
	for (size_t i = 0; i < builder.count; ++i) {
		auto& cell = builder.cells[i];
		size_t idx = cell.type.raw();
		inputs[idx] = cell.inputs;
		outputs[idx] = cell.outputs;
	}
}

constexpr Categories::Categories() {
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

constexpr PortInfo port_info;
constexpr Categories categories;

namespace Compat {
	constexpr Categories::Category internals_all = Categories::meet(categories.is_known, Categories::complement(categories.is_stdcell));
	constexpr Categories::Category mem_ff = Categories::join(categories.is_ff, categories.is_mem);
	// old setup_internals + setup_stdcells
	constexpr Categories::Category nomem_noff = Categories::meet(categories.is_known, Categories::complement(mem_ff));
	constexpr Categories::Category internals_mem_ff = Categories::meet(internals_all, mem_ff);
	// old setup_internals
	constexpr Categories::Category internals_nomem_noff = Categories::meet(internals_all, nomem_noff);
	// old setup_stdcells
	constexpr Categories::Category stdcells_nomem_noff = Categories::meet(categories.is_stdcell, nomem_noff);
	constexpr Categories::Category stdcells_mem = Categories::meet(categories.is_stdcell, categories.is_mem);
	// old setup_internals_eval
	// static constexpr auto internals_eval = Categories::meet(internals_all, categories.is_evaluable);
};

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

YOSYS_NAMESPACE_END
