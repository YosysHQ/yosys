#ifndef NEWCELLTYPES_H
#define NEWCELLTYPES_H

#include "kernel/rtlil.h"
#include "kernel/yosys.h"

YOSYS_NAMESPACE_BEGIN

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
		bool is_evaluable = false;
		bool is_combinatorial = false;
		bool is_synthesizable = false;
		bool is_stdcell = false;
		bool is_ff = false;
		bool is_mem_noff = false;
		bool is_anyinit = false;
		bool is_tristate = false;
	};
	struct CellInfo {
		RTLIL::IdString type;
		PortList inputs, outputs;
		Features features;
	};
	std::array<CellInfo, MAX_CELLS> cells{};
	size_t count = 0;

	constexpr void setup_type(RTLIL::IdString type, std::initializer_list<RTLIL::IdString> inputs, std::initializer_list<RTLIL::IdString> outputs, const Features& features) {
		cells[count++] = {type, PortList(inputs), PortList(outputs), features};
	}
	constexpr void setup_internals_other()
	{
		Features features {
			.is_tristate = true,
		};
		setup_type(ID($tribuf), {ID::A, ID::EN}, {ID::Y}, features);

		features = {};
		setup_type(ID($assert), {ID::A, ID::EN}, {}, features);
		setup_type(ID($assume), {ID::A, ID::EN}, {}, features);
		setup_type(ID($live), {ID::A, ID::EN}, {}, features);
		setup_type(ID($fair), {ID::A, ID::EN}, {}, features);
		setup_type(ID($cover), {ID::A, ID::EN}, {}, features);
		setup_type(ID($initstate), {}, {ID::Y}, features);
		setup_type(ID($anyconst), {}, {ID::Y}, features);
		setup_type(ID($anyseq), {}, {ID::Y}, features);
		setup_type(ID($allconst), {}, {ID::Y}, features);
		setup_type(ID($allseq), {}, {ID::Y}, features);
		setup_type(ID($equiv), {ID::A, ID::B}, {ID::Y}, features);
		setup_type(ID($specify2), {ID::EN, ID::SRC, ID::DST}, {}, features);
		setup_type(ID($specify3), {ID::EN, ID::SRC, ID::DST, ID::DAT}, {}, features);
		setup_type(ID($specrule), {ID::EN_SRC, ID::EN_DST, ID::SRC, ID::DST}, {}, features);
		setup_type(ID($print), {ID::EN, ID::ARGS, ID::TRG}, {}, features);
		setup_type(ID($check), {ID::A, ID::EN, ID::ARGS, ID::TRG}, {}, features);
		setup_type(ID($set_tag), {ID::A, ID::SET, ID::CLR}, {ID::Y}, features);
		setup_type(ID($get_tag), {ID::A}, {ID::Y}, features);
		setup_type(ID($overwrite_tag), {ID::A, ID::SET, ID::CLR}, {}, features);
		setup_type(ID($original_tag), {ID::A}, {ID::Y}, features);
		setup_type(ID($future_ff), {ID::A}, {ID::Y}, features);
		setup_type(ID($scopeinfo), {}, {}, features);
		setup_type(ID($input_port), {}, {ID::Y}, features);
		setup_type(ID($connect), {ID::A, ID::B}, {}, features);
	}
	constexpr void setup_internals_eval()
	{
		Features features {
			.is_evaluable = true,
		};
		std::initializer_list<RTLIL::IdString> unary_ops = {
			ID($not), ID($pos), ID($buf), ID($neg),
			ID($reduce_and), ID($reduce_or), ID($reduce_xor), ID($reduce_xnor), ID($reduce_bool),
			ID($logic_not), ID($slice), ID($lut), ID($sop)
		};

		std::initializer_list<RTLIL::IdString> binary_ops = {
			ID($and), ID($or), ID($xor), ID($xnor),
			ID($shl), ID($shr), ID($sshl), ID($sshr), ID($shift), ID($shiftx),
			ID($lt), ID($le), ID($eq), ID($ne), ID($eqx), ID($nex), ID($ge), ID($gt),
			ID($add), ID($sub), ID($mul), ID($div), ID($mod), ID($divfloor), ID($modfloor), ID($pow),
			ID($logic_and), ID($logic_or), ID($concat), ID($macc),
			ID($bweqx)
		};

		for (auto type : unary_ops)
			setup_type(type, {ID::A}, {ID::Y}, features);

		for (auto type : binary_ops)
			setup_type(type, {ID::A, ID::B}, {ID::Y}, features);

		for (auto type : {ID($mux), ID($pmux), ID($bwmux)})
			setup_type(type, {ID::A, ID::B, ID::S}, {ID::Y}, features);

		for (auto type : {ID($bmux), ID($demux)})
			setup_type(type, {ID::A, ID::S}, {ID::Y}, features);

		setup_type(ID($lcu), {ID::P, ID::G, ID::CI}, {ID::CO}, features);
		setup_type(ID($alu), {ID::A, ID::B, ID::CI, ID::BI}, {ID::X, ID::Y, ID::CO}, features);
		setup_type(ID($macc_v2), {ID::A, ID::B, ID::C}, {ID::Y}, features);
		setup_type(ID($fa), {ID::A, ID::B, ID::C}, {ID::X, ID::Y}, features);
	}
	constexpr void setup_internals_ff()
	{
		Features features {
			.is_ff = true,
		};
		setup_type(ID($sr), {ID::SET, ID::CLR}, {ID::Q}, features);
		setup_type(ID($ff), {ID::D}, {ID::Q}, features);
		setup_type(ID($dff), {ID::CLK, ID::D}, {ID::Q}, features);
		setup_type(ID($dffe), {ID::CLK, ID::EN, ID::D}, {ID::Q}, features);
		setup_type(ID($dffsr), {ID::CLK, ID::SET, ID::CLR, ID::D}, {ID::Q}, features);
		setup_type(ID($dffsre), {ID::CLK, ID::SET, ID::CLR, ID::D, ID::EN}, {ID::Q}, features);
		setup_type(ID($adff), {ID::CLK, ID::ARST, ID::D}, {ID::Q}, features);
		setup_type(ID($adffe), {ID::CLK, ID::ARST, ID::D, ID::EN}, {ID::Q}, features);
		setup_type(ID($aldff), {ID::CLK, ID::ALOAD, ID::AD, ID::D}, {ID::Q}, features);
		setup_type(ID($aldffe), {ID::CLK, ID::ALOAD, ID::AD, ID::D, ID::EN}, {ID::Q}, features);
		setup_type(ID($sdff), {ID::CLK, ID::SRST, ID::D}, {ID::Q}, features);
		setup_type(ID($sdffe), {ID::CLK, ID::SRST, ID::D, ID::EN}, {ID::Q}, features);
		setup_type(ID($sdffce), {ID::CLK, ID::SRST, ID::D, ID::EN}, {ID::Q}, features);
		setup_type(ID($dlatch), {ID::EN, ID::D}, {ID::Q}, features);
		setup_type(ID($adlatch), {ID::EN, ID::D, ID::ARST}, {ID::Q}, features);
		setup_type(ID($dlatchsr), {ID::EN, ID::SET, ID::CLR, ID::D}, {ID::Q}, features);
	}
	constexpr void setup_internals_anyinit()
	{
		Features features {
			.is_anyinit = true,
		};
		setup_type(ID($anyinit), {ID::D}, {ID::Q}, features);
	}
	constexpr void setup_internals_mem_noff()
	{
		Features features {
			.is_mem_noff = true,
		};
		// NOT setup_internals_ff()

		setup_type(ID($memrd), {ID::CLK, ID::EN, ID::ADDR}, {ID::DATA}, features);
		setup_type(ID($memrd_v2), {ID::CLK, ID::EN, ID::ARST, ID::SRST, ID::ADDR}, {ID::DATA}, features);
		setup_type(ID($memwr), {ID::CLK, ID::EN, ID::ADDR, ID::DATA}, {}, features);
		setup_type(ID($memwr_v2), {ID::CLK, ID::EN, ID::ADDR, ID::DATA}, {}, features);
		setup_type(ID($meminit), {ID::ADDR, ID::DATA}, {}, features);
		setup_type(ID($meminit_v2), {ID::ADDR, ID::DATA, ID::EN}, {}, features);
		setup_type(ID($mem), {ID::RD_CLK, ID::RD_EN, ID::RD_ADDR, ID::WR_CLK, ID::WR_EN, ID::WR_ADDR, ID::WR_DATA}, {ID::RD_DATA}, features);
		setup_type(ID($mem_v2), {ID::RD_CLK, ID::RD_EN, ID::RD_ARST, ID::RD_SRST, ID::RD_ADDR, ID::WR_CLK, ID::WR_EN, ID::WR_ADDR, ID::WR_DATA}, {ID::RD_DATA}, features);

		// What?
		setup_type(ID($fsm), {ID::CLK, ID::ARST, ID::CTRL_IN}, {ID::CTRL_OUT}, features);
	}
	constexpr void setup_stdcells_tristate()
	{
		Features features {
			.is_stdcell = true,
			.is_tristate = true,
		};
		setup_type(ID($_TBUF_), {ID::A, ID::E}, {ID::Y}, features);
	}

	constexpr void setup_stdcells_eval()
	{
		Features features {
			.is_evaluable = true,
			.is_stdcell = true,
		};
		setup_type(ID($_BUF_), {ID::A}, {ID::Y}, features);
		setup_type(ID($_NOT_), {ID::A}, {ID::Y}, features);
		setup_type(ID($_AND_), {ID::A, ID::B}, {ID::Y}, features);
		setup_type(ID($_NAND_), {ID::A, ID::B}, {ID::Y}, features);
		setup_type(ID($_OR_),  {ID::A, ID::B}, {ID::Y}, features);
		setup_type(ID($_NOR_),  {ID::A, ID::B}, {ID::Y}, features);
		setup_type(ID($_XOR_), {ID::A, ID::B}, {ID::Y}, features);
		setup_type(ID($_XNOR_), {ID::A, ID::B}, {ID::Y}, features);
		setup_type(ID($_ANDNOT_), {ID::A, ID::B}, {ID::Y}, features);
		setup_type(ID($_ORNOT_), {ID::A, ID::B}, {ID::Y}, features);
		setup_type(ID($_MUX_), {ID::A, ID::B, ID::S}, {ID::Y}, features);
		setup_type(ID($_NMUX_), {ID::A, ID::B, ID::S}, {ID::Y}, features);
		setup_type(ID($_MUX4_), {ID::A, ID::B, ID::C, ID::D, ID::S, ID::T}, {ID::Y}, features);
		setup_type(ID($_MUX8_), {ID::A, ID::B, ID::C, ID::D, ID::E, ID::F, ID::G, ID::H, ID::S, ID::T, ID::U}, {ID::Y}, features);
		setup_type(ID($_MUX16_), {ID::A, ID::B, ID::C, ID::D, ID::E, ID::F, ID::G, ID::H, ID::I, ID::J, ID::K, ID::L, ID::M, ID::N, ID::O, ID::P, ID::S, ID::T, ID::U, ID::V}, {ID::Y}, features);
		setup_type(ID($_AOI3_), {ID::A, ID::B, ID::C}, {ID::Y}, features);
		setup_type(ID($_OAI3_), {ID::A, ID::B, ID::C}, {ID::Y}, features);
		setup_type(ID($_AOI4_), {ID::A, ID::B, ID::C, ID::D}, {ID::Y}, features);
		setup_type(ID($_OAI4_), {ID::A, ID::B, ID::C, ID::D}, {ID::Y}, features);
	}

	constexpr void setup_stdcells_ff() {
		Features features {
			.is_stdcell = true,
			.is_ff = true,
		};

		// for (auto c1 : list_np)
		// for (auto c2 : list_np)
		// 	setup_type(std::string("$_SR_") + c1 + c2 + "_", {ID::S, ID::R}, {ID::Q}, features);
		setup_type(ID($_SR_NN_), {ID::S, ID::R}, {ID::Q}, features);
		setup_type(ID($_SR_NP_), {ID::S, ID::R}, {ID::Q}, features);
		setup_type(ID($_SR_PN_), {ID::S, ID::R}, {ID::Q}, features);
		setup_type(ID($_SR_PP_), {ID::S, ID::R}, {ID::Q}, features);

		setup_type(ID($_FF_), {ID::D}, {ID::Q}, features);

		// for (auto c1 : list_np)
		// 	setup_type(std::string("$_DFF_") + c1 + "_", {ID::C, ID::D}, {ID::Q}, features);
		setup_type(ID::$_DFF_N_, {ID::C, ID::D}, {ID::Q}, features);
		setup_type(ID::$_DFF_P_, {ID::C, ID::D}, {ID::Q}, features);

		// for (auto c1 : list_np)
		// for (auto c2 : list_np)
		// 	setup_type(std::string("$_DFFE_") + c1 + c2 + "_", {ID::C, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID::$_DFFE_NN_, {ID::C, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID::$_DFFE_NP_, {ID::C, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID::$_DFFE_PN_, {ID::C, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID::$_DFFE_PP_, {ID::C, ID::D, ID::E}, {ID::Q}, features);
		// for (auto c1 : list_np)
		// for (auto c2 : list_np)
		// for (auto c3 : list_01)
		// 	setup_type(std::string("$_DFF_") + c1 + c2 + c3 + "_", {ID::C, ID::R, ID::D}, {ID::Q}, features);
		setup_type(ID($_DFF_NN0_), {ID::C, ID::R, ID::D}, {ID::Q}, features);
		setup_type(ID($_DFF_NN1_), {ID::C, ID::R, ID::D}, {ID::Q}, features);
		setup_type(ID($_DFF_NP0_), {ID::C, ID::R, ID::D}, {ID::Q}, features);
		setup_type(ID($_DFF_NP1_), {ID::C, ID::R, ID::D}, {ID::Q}, features);
		setup_type(ID($_DFF_PN0_), {ID::C, ID::R, ID::D}, {ID::Q}, features);
		setup_type(ID($_DFF_PN1_), {ID::C, ID::R, ID::D}, {ID::Q}, features);
		setup_type(ID($_DFF_PP0_), {ID::C, ID::R, ID::D}, {ID::Q}, features);
		setup_type(ID($_DFF_PP1_), {ID::C, ID::R, ID::D}, {ID::Q}, features);
		// for (auto c1 : list_np)
		// for (auto c2 : list_np)
		// for (auto c3 : list_01)
		// for (auto c4 : list_np)
		// 	setup_type(std::string("$_DFFE_") + c1 + c2 + c3 + c4 + "_", {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_DFFE_NN0N_), {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_DFFE_NN0P_), {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_DFFE_NN1N_), {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_DFFE_NN1P_), {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_DFFE_NP0N_), {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_DFFE_NP0P_), {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_DFFE_NP1N_), {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_DFFE_NP1P_), {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_DFFE_PN0N_), {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_DFFE_PN0P_), {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_DFFE_PN1N_), {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_DFFE_PN1P_), {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_DFFE_PP0N_), {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_DFFE_PP0P_), {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_DFFE_PP1N_), {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_DFFE_PP1P_), {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		// for (auto c1 : list_np)
		// for (auto c2 : list_np)
		// 	setup_type(std::string("$_ALDFF_") + c1 + c2 + "_", {ID::C, ID::L, ID::AD, ID::D}, {ID::Q}, features);
		setup_type(ID($_ALDFF_NN_), {ID::C, ID::L, ID::AD, ID::D}, {ID::Q}, features);
		setup_type(ID($_ALDFF_NP_), {ID::C, ID::L, ID::AD, ID::D}, {ID::Q}, features);
		setup_type(ID($_ALDFF_PN_), {ID::C, ID::L, ID::AD, ID::D}, {ID::Q}, features);
		setup_type(ID($_ALDFF_PP_), {ID::C, ID::L, ID::AD, ID::D}, {ID::Q}, features);
		// for (auto c1 : list_np)
		// for (auto c2 : list_np)
		// for (auto c3 : list_np)
		// 	setup_type(std::string("$_ALDFFE_") + c1 + c2 + c3 + "_", {ID::C, ID::L, ID::AD, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_ALDFFE_NNN_), {ID::C, ID::L, ID::AD, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_ALDFFE_NNP_), {ID::C, ID::L, ID::AD, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_ALDFFE_NPN_), {ID::C, ID::L, ID::AD, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_ALDFFE_NPP_), {ID::C, ID::L, ID::AD, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_ALDFFE_PNN_), {ID::C, ID::L, ID::AD, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_ALDFFE_PNP_), {ID::C, ID::L, ID::AD, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_ALDFFE_PPN_), {ID::C, ID::L, ID::AD, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_ALDFFE_PPP_), {ID::C, ID::L, ID::AD, ID::D, ID::E}, {ID::Q}, features);
		// for (auto c1 : list_np)
		// for (auto c2 : list_np)
		// for (auto c3 : list_np)
		// 	setup_type(std::string("$_DFFSR_") + c1 + c2 + c3 + "_", {ID::C, ID::S, ID::R, ID::D}, {ID::Q}, features);
		setup_type(ID($_DFFSR_NNN_), {ID::C, ID::S, ID::R, ID::D}, {ID::Q}, features);
		setup_type(ID($_DFFSR_NNP_), {ID::C, ID::S, ID::R, ID::D}, {ID::Q}, features);
		setup_type(ID($_DFFSR_NPN_), {ID::C, ID::S, ID::R, ID::D}, {ID::Q}, features);
		setup_type(ID($_DFFSR_NPP_), {ID::C, ID::S, ID::R, ID::D}, {ID::Q}, features);
		setup_type(ID($_DFFSR_PNN_), {ID::C, ID::S, ID::R, ID::D}, {ID::Q}, features);
		setup_type(ID($_DFFSR_PNP_), {ID::C, ID::S, ID::R, ID::D}, {ID::Q}, features);
		setup_type(ID($_DFFSR_PPN_), {ID::C, ID::S, ID::R, ID::D}, {ID::Q}, features);
		setup_type(ID($_DFFSR_PPP_), {ID::C, ID::S, ID::R, ID::D}, {ID::Q}, features);
		// for (auto c1 : list_np)
		// for (auto c2 : list_np)
		// for (auto c3 : list_np)
		// for (auto c4 : list_np)
		// 	setup_type(std::string("$_DFFSRE_") + c1 + c2 + c3 + c4 + "_", {ID::C, ID::S, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_DFFSRE_NNNN_), {ID::C, ID::S, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_DFFSRE_NNNP_), {ID::C, ID::S, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_DFFSRE_NNPN_), {ID::C, ID::S, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_DFFSRE_NNPP_), {ID::C, ID::S, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_DFFSRE_NPNN_), {ID::C, ID::S, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_DFFSRE_NPNP_), {ID::C, ID::S, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_DFFSRE_NPPN_), {ID::C, ID::S, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_DFFSRE_NPPP_), {ID::C, ID::S, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_DFFSRE_PNNN_), {ID::C, ID::S, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_DFFSRE_PNNP_), {ID::C, ID::S, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_DFFSRE_PNPN_), {ID::C, ID::S, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_DFFSRE_PNPP_), {ID::C, ID::S, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_DFFSRE_PPNN_), {ID::C, ID::S, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_DFFSRE_PPNP_), {ID::C, ID::S, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_DFFSRE_PPPN_), {ID::C, ID::S, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_DFFSRE_PPPP_), {ID::C, ID::S, ID::R, ID::D, ID::E}, {ID::Q}, features);
		// for (auto c1 : list_np)
		// for (auto c2 : list_np)
		// for (auto c3 : list_01)
		// 	setup_type(std::string("$_SDFF_") + c1 + c2 + c3 + "_", {ID::C, ID::R, ID::D}, {ID::Q}, features);
		setup_type(ID($_SDFF_NN0_), {ID::C, ID::R, ID::D}, {ID::Q}, features);
		setup_type(ID($_SDFF_NN1_), {ID::C, ID::R, ID::D}, {ID::Q}, features);
		setup_type(ID($_SDFF_NP0_), {ID::C, ID::R, ID::D}, {ID::Q}, features);
		setup_type(ID($_SDFF_NP1_), {ID::C, ID::R, ID::D}, {ID::Q}, features);
		setup_type(ID($_SDFF_PN0_), {ID::C, ID::R, ID::D}, {ID::Q}, features);
		setup_type(ID($_SDFF_PN1_), {ID::C, ID::R, ID::D}, {ID::Q}, features);
		setup_type(ID($_SDFF_PP0_), {ID::C, ID::R, ID::D}, {ID::Q}, features);
		setup_type(ID($_SDFF_PP1_), {ID::C, ID::R, ID::D}, {ID::Q}, features);
		// for (auto c1 : list_np)
		// for (auto c2 : list_np)
		// for (auto c3 : list_01)
		// for (auto c4 : list_np)
		// 	setup_type(std::string("$_SDFFE_") + c1 + c2 + c3 + c4 + "_", {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_SDFFE_NN0N_), {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_SDFFE_NN0P_), {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_SDFFE_NN1N_), {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_SDFFE_NN1P_), {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_SDFFE_NP0N_), {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_SDFFE_NP0P_), {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_SDFFE_NP1N_), {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_SDFFE_NP1P_), {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_SDFFE_PN0N_), {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_SDFFE_PN0P_), {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_SDFFE_PN1N_), {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_SDFFE_PN1P_), {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_SDFFE_PP0N_), {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_SDFFE_PP0P_), {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_SDFFE_PP1N_), {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_SDFFE_PP1P_), {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		// for (auto c1 : list_np)
		// for (auto c2 : list_np)
		// for (auto c3 : list_01)
		// for (auto c4 : list_np)
		// 	setup_type(std::string("$_SDFFCE_") + c1 + c2 + c3 + c4 + "_", {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_SDFFCE_NN0N_), {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_SDFFCE_NN0P_), {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_SDFFCE_NN1N_), {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_SDFFCE_NN1P_), {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_SDFFCE_NP0N_), {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_SDFFCE_NP0P_), {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_SDFFCE_NP1N_), {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_SDFFCE_NP1P_), {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_SDFFCE_PN0N_), {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_SDFFCE_PN0P_), {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_SDFFCE_PN1N_), {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_SDFFCE_PN1P_), {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_SDFFCE_PP0N_), {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_SDFFCE_PP0P_), {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_SDFFCE_PP1N_), {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		setup_type(ID($_SDFFCE_PP1P_), {ID::C, ID::R, ID::D, ID::E}, {ID::Q}, features);
		// for (auto c1 : list_np)
		// 	setup_type(std::string("$_DLATCH_") + c1 + "_", {ID::E, ID::D}, {ID::Q}, features);
		setup_type(ID($_DLATCH_N_), {ID::E, ID::D}, {ID::Q}, features);
		setup_type(ID($_DLATCH_P_), {ID::E, ID::D}, {ID::Q}, features);

		// for (auto c1 : list_np)
		// for (auto c2 : list_np)
		// for (auto c3 : list_01)
		// 	setup_type(std::string("$_DLATCH_") + c1 + c2 + c3 + "_", {ID::E, ID::R, ID::D}, {ID::Q}, features);
		setup_type(ID($_DLATCH_NN0_), {ID::E, ID::R, ID::D}, {ID::Q}, features);
		setup_type(ID($_DLATCH_NN1_), {ID::E, ID::R, ID::D}, {ID::Q}, features);
		setup_type(ID($_DLATCH_NP0_), {ID::E, ID::R, ID::D}, {ID::Q}, features);
		setup_type(ID($_DLATCH_NP1_), {ID::E, ID::R, ID::D}, {ID::Q}, features);
		setup_type(ID($_DLATCH_PN0_), {ID::E, ID::R, ID::D}, {ID::Q}, features);
		setup_type(ID($_DLATCH_PN1_), {ID::E, ID::R, ID::D}, {ID::Q}, features);
		setup_type(ID($_DLATCH_PP0_), {ID::E, ID::R, ID::D}, {ID::Q}, features);
		setup_type(ID($_DLATCH_PP1_), {ID::E, ID::R, ID::D}, {ID::Q}, features);
		// for (auto c1 : list_np)
		// for (auto c2 : list_np)
		// for (auto c3 : list_np)
		// 	setup_type(std::string("$_DLATCHSR_") + c1 + c2 + c3 + "_", {ID::E, ID::S, ID::R, ID::D}, {ID::Q}, features);
		setup_type(ID($_DLATCHSR_NNN_), {ID::E, ID::S, ID::R, ID::D}, {ID::Q}, features);
		setup_type(ID($_DLATCHSR_NNP_), {ID::E, ID::S, ID::R, ID::D}, {ID::Q}, features);
		setup_type(ID($_DLATCHSR_NPN_), {ID::E, ID::S, ID::R, ID::D}, {ID::Q}, features);
		setup_type(ID($_DLATCHSR_NPP_), {ID::E, ID::S, ID::R, ID::D}, {ID::Q}, features);
		setup_type(ID($_DLATCHSR_PNN_), {ID::E, ID::S, ID::R, ID::D}, {ID::Q}, features);
		setup_type(ID($_DLATCHSR_PNP_), {ID::E, ID::S, ID::R, ID::D}, {ID::Q}, features);
		setup_type(ID($_DLATCHSR_PPN_), {ID::E, ID::S, ID::R, ID::D}, {ID::Q}, features);
		setup_type(ID($_DLATCHSR_PPP_), {ID::E, ID::S, ID::R, ID::D}, {ID::Q}, features);
	}
	constexpr CellTableBuilder() {
		setup_internals_other();
		setup_internals_eval();
		setup_internals_ff();
		setup_internals_anyinit();
		setup_internals_mem_noff();
		setup_stdcells_tristate();
		setup_stdcells_eval();
		setup_stdcells_ff();
	}

};


constexpr CellTableBuilder turbo_builder{};

// template<typename T>
// struct Worlds {
// 	struct World {
// 		std::array<T, MAX_CELLS> data{};
// 		constexpr T operator()(IdString type) const {
// 			return data[type.index_];
// 		}
// 		constexpr T& operator[](size_t idx) {
// 			return data[idx];
// 		}
// 		constexpr size_t size() const { return data.size(); }
// 	};
// 	World is_known {};
// 	World is_evaluable {};
// 	World is_combinatorial {};
// 	World is_synthesizable {};
// 	World is_stdcell {};
// 	World is_ff {};
// 	World is_mem_noff {};
// 	World is_anyinit {};
// 	World is_tristate {};
// 	virtual constexpr Categories();
// };

struct PortInfo {
	struct PortLists {
		std::array<CellTableBuilder::PortList, MAX_CELLS> data{};
		constexpr CellTableBuilder::PortList operator()(IdString type) const {
			return data[type.index_];
		}
		constexpr CellTableBuilder::PortList& operator[](size_t idx) {
			return data[idx];
		}
		constexpr size_t size() const { return data.size(); }
	};
	PortLists inputs {};
	PortLists outputs {};
	constexpr PortInfo() {
		for (size_t i = 0; i < turbo_builder.count; ++i) {
			auto& cell = turbo_builder.cells[i];
			size_t idx = cell.type.index_;
			inputs[idx] = cell.inputs;
			outputs[idx] = cell.outputs;
		}
	}
};

struct Categories {
	struct Category {
		std::array<bool, MAX_CELLS> data{};
		constexpr bool operator()(IdString type) const {
			size_t idx = type.index_;
			if (idx >= MAX_CELLS)
				return false;
			return data[idx];
		}
		constexpr bool operator[](size_t idx) {
			return data[idx];
		}
		constexpr void set_id(IdString type, bool val = true) {
			size_t idx = type.index_;
			if (idx >= MAX_CELLS)
				return; // TODO should be an assert but then it's not constexpr
			data[idx] = val;
		}
		constexpr void set(size_t idx, bool val = true) {
			data[idx] = val;
		}
		constexpr size_t size() const { return data.size(); }
	};
	Category empty {};
	Category is_known {};
	Category is_evaluable {};
	Category is_combinatorial {};
	Category is_synthesizable {};
	Category is_stdcell {};
	Category is_ff {};
	Category is_mem_noff {};
	Category is_anyinit {};
	Category is_tristate {};
	constexpr Categories() {
		for (size_t i = 0; i < turbo_builder.count; ++i) {
			auto& cell = turbo_builder.cells[i];
			size_t idx = cell.type.index_;
			is_known.set(idx);
			is_evaluable.set(idx, cell.features.is_evaluable);
			is_combinatorial.set(idx, cell.features.is_combinatorial);
			is_synthesizable.set(idx, cell.features.is_synthesizable);
			is_stdcell.set(idx, cell.features.is_stdcell);
			is_ff.set(idx, cell.features.is_ff);
			is_mem_noff.set(idx, cell.features.is_mem_noff);
			is_anyinit.set(idx, cell.features.is_anyinit);
			is_tristate.set(idx, cell.features.is_tristate);
		}
	}
	constexpr static Category join(Category left, Category right) {
		Category c {};
		for (size_t i = 0; i < MAX_CELLS; ++i) {
			c.set(i, left[i] || right[i]);
		}
		return c;
	}
	constexpr static Category meet(Category left, Category right) {
		Category c {};
		for (size_t i = 0; i < MAX_CELLS; ++i) {
			c.set(i, left[i] && right[i]);
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
};

// Pure
static constexpr PortInfo port_info;
static constexpr Categories categories;

// Legacy
namespace Compat {
	static constexpr auto internals_all = Categories::meet(categories.is_known, Categories::complement(categories.is_stdcell));
	static constexpr auto mem_ff = Categories::join(categories.is_ff, categories.is_mem_noff);
	static constexpr auto nomem_noff = Categories::meet(categories.is_known, Categories::complement(mem_ff));
	static constexpr auto internals_mem_ff = Categories::meet(internals_all, mem_ff);
	// old setup_internals
	static constexpr auto internals_nomem_noff = Categories::meet(internals_all, nomem_noff);
	static constexpr auto stdcells_mem = Categories::meet(categories.is_stdcell, categories.is_mem_noff);
};

namespace {
	static_assert(categories.is_evaluable(ID($and)));
	static_assert(!categories.is_ff(ID($and)));
	static_assert(Categories::join(categories.is_evaluable, categories.is_ff)(ID($and)));
	static_assert(Categories::join(categories.is_evaluable, categories.is_ff)(ID($dffsr)));
	static_assert(!Categories::join(categories.is_evaluable, categories.is_ff)(ID($anyinit)));
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
	dict<RTLIL::IdString, NewCellType> custom_cell_types = {};

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
		pool<RTLIL::IdString> inputs, outputs;
		for (RTLIL::IdString wire_name : module->ports) {
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

	bool cell_known(const RTLIL::IdString &type) const {
		return static_cell_types(type) || custom_cell_types.count(type) != 0;
	}

	bool cell_output(const RTLIL::IdString &type, const RTLIL::IdString &port) const
	{
		if (static_cell_types(type) && StaticCellTypes::port_info.outputs(type).contains(port)) {
			return true;
		}
		auto it = custom_cell_types.find(type);
		return it != custom_cell_types.end() && it->second.outputs.count(port) != 0;
	}

	bool cell_input(const RTLIL::IdString &type, const RTLIL::IdString &port) const
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
	bool cell_evaluable(const RTLIL::IdString &type) const
	{
		return static_cell_types(type) && StaticCellTypes::categories.is_evaluable(type);
	}
};

YOSYS_NAMESPACE_END

#endif
