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
		std::array<TwineRef, MAX_PORTS> ports{};
		size_t count = 0;
		constexpr PortList() = default;
		constexpr PortList(std::initializer_list<TwineRef> init) {
			for (auto p : init) {
				ports[count++] = p;
			}
		}
		constexpr auto begin() const { return ports.begin(); }
		constexpr auto end() const { return ports.begin() + count; }
		constexpr bool contains(TwineRef port) const {
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
		TwineRef type;
		PortList inputs, outputs;
		Features features;
	};
	std::array<CellInfo, MAX_CELLS> cells{};
	size_t count = 0;

	constexpr void setup_type(TwineRef type, std::initializer_list<TwineRef> inputs, std::initializer_list<TwineRef> outputs, const Features& features) {
		cells[count++] = {type, PortList(inputs), PortList(outputs), features};
	}
	constexpr void setup_internals_other()
	{
		Features features {};
		features.is_tristate = true;
		setup_type(TW($tribuf), {TW::A, TW::EN}, {TW::Y}, features);

		features = {};
		setup_type(TW($assert), {TW::A, TW::EN}, {}, features);
		setup_type(TW($assume), {TW::A, TW::EN}, {}, features);
		setup_type(TW($live), {TW::A, TW::EN}, {}, features);
		setup_type(TW($fair), {TW::A, TW::EN}, {}, features);
		setup_type(TW($cover), {TW::A, TW::EN}, {}, features);
		setup_type(TW($initstate), {}, {TW::Y}, features);
		setup_type(TW($anyconst), {}, {TW::Y}, features);
		setup_type(TW($anyseq), {}, {TW::Y}, features);
		setup_type(TW($allconst), {}, {TW::Y}, features);
		setup_type(TW($allseq), {}, {TW::Y}, features);
		setup_type(TW($equiv), {TW::A, TW::B}, {TW::Y}, features);
		setup_type(TW($specify2), {TW::EN, TW::SRC, TW::DST}, {}, features);
		setup_type(TW($specify3), {TW::EN, TW::SRC, TW::DST, TW::DAT}, {}, features);
		setup_type(TW($specrule), {TW::SRC_EN, TW::DST_EN, TW::SRC, TW::DST}, {}, features);
		setup_type(TW($print), {TW::EN, TW::ARGS, TW::TRG}, {}, features);
		setup_type(TW($check), {TW::A, TW::EN, TW::ARGS, TW::TRG}, {}, features);
		setup_type(TW($set_tag), {TW::A, TW::SET, TW::CLR}, {TW::Y}, features);
		setup_type(TW($get_tag), {TW::A}, {TW::Y}, features);
		setup_type(TW($overwrite_tag), {TW::A, TW::SET, TW::CLR}, {}, features);
		setup_type(TW($original_tag), {TW::A}, {TW::Y}, features);
		setup_type(TW($future_ff), {TW::A}, {TW::Y}, features);
		setup_type(TW($scopeinfo), {}, {}, features);
		setup_type(TW($input_port), {}, {TW::Y}, features);
		setup_type(TW($output_port), {TW::A}, {}, features);
		setup_type(TW($public), {TW::A}, {}, features);
		setup_type(TW($connect), {TW::A, TW::B}, {}, features);
	}
	constexpr void setup_internals_eval()
	{
		Features features {};
		features.is_evaluable = true;
		std::initializer_list<TwineRef> unary_ops = {
			TW($not), TW($pos), TW($buf), TW($neg),
			TW($reduce_and), TW($reduce_or), TW($reduce_xor), TW($reduce_xnor), TW($reduce_bool),
			TW($logic_not), TW($slice), TW($lut), TW($sop)
		};

		std::initializer_list<TwineRef> binary_ops = {
			TW($and), TW($or), TW($xor), TW($xnor),
			TW($shl), TW($shr), TW($sshl), TW($sshr), TW($shift), TW($shiftx),
			TW($lt), TW($le), TW($eq), TW($ne), TW($eqx), TW($nex), TW($ge), TW($gt),
			TW($add), TW($sub), TW($mul), TW($div), TW($mod), TW($divfloor), TW($modfloor), TW($pow),
			TW($logic_and), TW($logic_or), TW($concat), TW($macc),
			TW($bweqx)
		};

		for (auto type : unary_ops)
			setup_type(type, {TW::A}, {TW::Y}, features);

		for (auto type : binary_ops)
			setup_type(type, {TW::A, TW::B}, {TW::Y}, features);

		for (auto type : {TW($mux), TW($pmux), TW($bwmux)})
			setup_type(type, {TW::A, TW::B, TW::S}, {TW::Y}, features);

		for (auto type : {TW($bmux), TW($demux)})
			setup_type(type, {TW::A, TW::S}, {TW::Y}, features);

		setup_type(TW($lcu), {TW::P, TW::G, TW::CI}, {TW::CO}, features);
		setup_type(TW($alu), {TW::A, TW::B, TW::CI, TW::BI}, {TW::X, TW::Y, TW::CO}, features);
		setup_type(TW($macc_v2), {TW::A, TW::B, TW::C}, {TW::Y}, features);
		setup_type(TW($fa), {TW::A, TW::B, TW::C}, {TW::X, TW::Y}, features);
	}
	constexpr void setup_internals_ff()
	{
		Features features {};
		features.is_ff = true;
		setup_type(TW($sr), {TW::SET, TW::CLR}, {TW::Q}, features);
		setup_type(TW($ff), {TW::D}, {TW::Q}, features);
		setup_type(TW($dff), {TW::CLK, TW::D}, {TW::Q}, features);
		setup_type(TW($dffe), {TW::CLK, TW::EN, TW::D}, {TW::Q}, features);
		setup_type(TW($dffsr), {TW::CLK, TW::SET, TW::CLR, TW::D}, {TW::Q}, features);
		setup_type(TW($dffsre), {TW::CLK, TW::SET, TW::CLR, TW::D, TW::EN}, {TW::Q}, features);
		setup_type(TW($adff), {TW::CLK, TW::ARST, TW::D}, {TW::Q}, features);
		setup_type(TW($adffe), {TW::CLK, TW::ARST, TW::D, TW::EN}, {TW::Q}, features);
		setup_type(TW($aldff), {TW::CLK, TW::ALOAD, TW::AD, TW::D}, {TW::Q}, features);
		setup_type(TW($aldffe), {TW::CLK, TW::ALOAD, TW::AD, TW::D, TW::EN}, {TW::Q}, features);
		setup_type(TW($sdff), {TW::CLK, TW::SRST, TW::D}, {TW::Q}, features);
		setup_type(TW($sdffe), {TW::CLK, TW::SRST, TW::D, TW::EN}, {TW::Q}, features);
		setup_type(TW($sdffce), {TW::CLK, TW::SRST, TW::D, TW::EN}, {TW::Q}, features);
		setup_type(TW($dlatch), {TW::EN, TW::D}, {TW::Q}, features);
		setup_type(TW($adlatch), {TW::EN, TW::D, TW::ARST}, {TW::Q}, features);
		setup_type(TW($dlatchsr), {TW::EN, TW::SET, TW::CLR, TW::D}, {TW::Q}, features);
	}
	constexpr void setup_internals_anyinit()
	{
		Features features {};
		features.is_anyinit = true;
		setup_type(TW($anyinit), {TW::D}, {TW::Q}, features);
	}
	constexpr void setup_internals_mem_noff()
	{
		Features features {};
		features.is_mem_noff = true;
		// NOT setup_internals_ff()

		setup_type(TW($memrd), {TW::CLK, TW::EN, TW::ADDR}, {TW::DATA}, features);
		setup_type(TW($memrd_v2), {TW::CLK, TW::EN, TW::ARST, TW::SRST, TW::ADDR}, {TW::DATA}, features);
		setup_type(TW($memwr), {TW::CLK, TW::EN, TW::ADDR, TW::DATA}, {}, features);
		setup_type(TW($memwr_v2), {TW::CLK, TW::EN, TW::ADDR, TW::DATA}, {}, features);
		setup_type(TW($meminit), {TW::ADDR, TW::DATA}, {}, features);
		setup_type(TW($meminit_v2), {TW::ADDR, TW::DATA, TW::EN}, {}, features);
		setup_type(TW($mem), {TW::RD_CLK, TW::RD_EN, TW::RD_ADDR, TW::WR_CLK, TW::WR_EN, TW::WR_ADDR, TW::WR_DATA}, {TW::RD_DATA}, features);
		setup_type(TW($mem_v2), {TW::RD_CLK, TW::RD_EN, TW::RD_ARST, TW::RD_SRST, TW::RD_ADDR, TW::WR_CLK, TW::WR_EN, TW::WR_ADDR, TW::WR_DATA}, {TW::RD_DATA}, features);

		// What?
		setup_type(TW($fsm), {TW::CLK, TW::ARST, TW::CTRL_IN}, {TW::CTRL_OUT}, features);
	}
	constexpr void setup_stdcells_tristate()
	{
		Features features {};
		features.is_stdcell = true;
		features.is_tristate = true;
		setup_type(TW($_TBUF_), {TW::A, TW::E}, {TW::Y}, features);
	}

	constexpr void setup_stdcells_eval()
	{
		Features features {};
		features.is_stdcell = true;
		features.is_evaluable = true;
		setup_type(TW($_BUF_), {TW::A}, {TW::Y}, features);
		setup_type(TW($_NOT_), {TW::A}, {TW::Y}, features);
		setup_type(TW($_AND_), {TW::A, TW::B}, {TW::Y}, features);
		setup_type(TW($_NAND_), {TW::A, TW::B}, {TW::Y}, features);
		setup_type(TW($_OR_),  {TW::A, TW::B}, {TW::Y}, features);
		setup_type(TW($_NOR_),  {TW::A, TW::B}, {TW::Y}, features);
		setup_type(TW($_XOR_), {TW::A, TW::B}, {TW::Y}, features);
		setup_type(TW($_XNOR_), {TW::A, TW::B}, {TW::Y}, features);
		setup_type(TW($_ANDNOT_), {TW::A, TW::B}, {TW::Y}, features);
		setup_type(TW($_ORNOT_), {TW::A, TW::B}, {TW::Y}, features);
		setup_type(TW($_MUX_), {TW::A, TW::B, TW::S}, {TW::Y}, features);
		setup_type(TW($_NMUX_), {TW::A, TW::B, TW::S}, {TW::Y}, features);
		setup_type(TW($_MUX4_), {TW::A, TW::B, TW::C, TW::D, TW::S, TW::T}, {TW::Y}, features);
		setup_type(TW($_MUX8_), {TW::A, TW::B, TW::C, TW::D, TW::E, TW::F, TW::G, TW::H, TW::S, TW::T, TW::U}, {TW::Y}, features);
		setup_type(TW($_MUX16_), {TW::A, TW::B, TW::C, TW::D, TW::E, TW::F, TW::G, TW::H, TW::I, TW::J, TW::K, TW::L, TW::M, TW::N, TW::O, TW::P, TW::S, TW::T, TW::U, TW::V}, {TW::Y}, features);
		setup_type(TW($_AOI3_), {TW::A, TW::B, TW::C}, {TW::Y}, features);
		setup_type(TW($_OAI3_), {TW::A, TW::B, TW::C}, {TW::Y}, features);
		setup_type(TW($_AOI4_), {TW::A, TW::B, TW::C, TW::D}, {TW::Y}, features);
		setup_type(TW($_OAI4_), {TW::A, TW::B, TW::C, TW::D}, {TW::Y}, features);
	}

	constexpr void setup_stdcells_ff() {
		Features features {};
		features.is_stdcell = true;
		features.is_ff = true;

		// for (auto c1 : list_np)
		// for (auto c2 : list_np)
		// 	setup_type(std::string("$_SR_") + c1 + c2 + "_", {TW::S, TW::R}, {TW::Q}, features);
		setup_type(TW($_SR_NN_), {TW::S, TW::R}, {TW::Q}, features);
		setup_type(TW($_SR_NP_), {TW::S, TW::R}, {TW::Q}, features);
		setup_type(TW($_SR_PN_), {TW::S, TW::R}, {TW::Q}, features);
		setup_type(TW($_SR_PP_), {TW::S, TW::R}, {TW::Q}, features);

		setup_type(TW($_FF_), {TW::D}, {TW::Q}, features);

		// for (auto c1 : list_np)
		// 	setup_type(std::string("$_DFF_") + c1 + "_", {TW::C, TW::D}, {TW::Q}, features);
		setup_type(TW($_DFF_N_), {TW::C, TW::D}, {TW::Q}, features);
		setup_type(TW($_DFF_P_), {TW::C, TW::D}, {TW::Q}, features);

		// for (auto c1 : list_np)
		// for (auto c2 : list_np)
		// 	setup_type(std::string("$_DFFE_") + c1 + c2 + "_", {TW::C, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_DFFE_NN_), {TW::C, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_DFFE_NP_), {TW::C, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_DFFE_PN_), {TW::C, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_DFFE_PP_), {TW::C, TW::D, TW::E}, {TW::Q}, features);
		// for (auto c1 : list_np)
		// for (auto c2 : list_np)
		// for (auto c3 : list_01)
		// 	setup_type(std::string("$_DFF_") + c1 + c2 + c3 + "_", {TW::C, TW::R, TW::D}, {TW::Q}, features);
		setup_type(TW($_DFF_NN0_), {TW::C, TW::R, TW::D}, {TW::Q}, features);
		setup_type(TW($_DFF_NN1_), {TW::C, TW::R, TW::D}, {TW::Q}, features);
		setup_type(TW($_DFF_NP0_), {TW::C, TW::R, TW::D}, {TW::Q}, features);
		setup_type(TW($_DFF_NP1_), {TW::C, TW::R, TW::D}, {TW::Q}, features);
		setup_type(TW($_DFF_PN0_), {TW::C, TW::R, TW::D}, {TW::Q}, features);
		setup_type(TW($_DFF_PN1_), {TW::C, TW::R, TW::D}, {TW::Q}, features);
		setup_type(TW($_DFF_PP0_), {TW::C, TW::R, TW::D}, {TW::Q}, features);
		setup_type(TW($_DFF_PP1_), {TW::C, TW::R, TW::D}, {TW::Q}, features);
		// for (auto c1 : list_np)
		// for (auto c2 : list_np)
		// for (auto c3 : list_01)
		// for (auto c4 : list_np)
		// 	setup_type(std::string("$_DFFE_") + c1 + c2 + c3 + c4 + "_", {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_DFFE_NN0N_), {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_DFFE_NN0P_), {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_DFFE_NN1N_), {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_DFFE_NN1P_), {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_DFFE_NP0N_), {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_DFFE_NP0P_), {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_DFFE_NP1N_), {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_DFFE_NP1P_), {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_DFFE_PN0N_), {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_DFFE_PN0P_), {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_DFFE_PN1N_), {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_DFFE_PN1P_), {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_DFFE_PP0N_), {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_DFFE_PP0P_), {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_DFFE_PP1N_), {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_DFFE_PP1P_), {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		// for (auto c1 : list_np)
		// for (auto c2 : list_np)
		// 	setup_type(std::string("$_ALDFF_") + c1 + c2 + "_", {TW::C, TW::L, TW::AD, TW::D}, {TW::Q}, features);
		setup_type(TW($_ALDFF_NN_), {TW::C, TW::L, TW::AD, TW::D}, {TW::Q}, features);
		setup_type(TW($_ALDFF_NP_), {TW::C, TW::L, TW::AD, TW::D}, {TW::Q}, features);
		setup_type(TW($_ALDFF_PN_), {TW::C, TW::L, TW::AD, TW::D}, {TW::Q}, features);
		setup_type(TW($_ALDFF_PP_), {TW::C, TW::L, TW::AD, TW::D}, {TW::Q}, features);
		// for (auto c1 : list_np)
		// for (auto c2 : list_np)
		// for (auto c3 : list_np)
		// 	setup_type(std::string("$_ALDFFE_") + c1 + c2 + c3 + "_", {TW::C, TW::L, TW::AD, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_ALDFFE_NNN_), {TW::C, TW::L, TW::AD, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_ALDFFE_NNP_), {TW::C, TW::L, TW::AD, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_ALDFFE_NPN_), {TW::C, TW::L, TW::AD, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_ALDFFE_NPP_), {TW::C, TW::L, TW::AD, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_ALDFFE_PNN_), {TW::C, TW::L, TW::AD, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_ALDFFE_PNP_), {TW::C, TW::L, TW::AD, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_ALDFFE_PPN_), {TW::C, TW::L, TW::AD, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_ALDFFE_PPP_), {TW::C, TW::L, TW::AD, TW::D, TW::E}, {TW::Q}, features);
		// for (auto c1 : list_np)
		// for (auto c2 : list_np)
		// for (auto c3 : list_np)
		// 	setup_type(std::string("$_DFFSR_") + c1 + c2 + c3 + "_", {TW::C, TW::S, TW::R, TW::D}, {TW::Q}, features);
		setup_type(TW($_DFFSR_NNN_), {TW::C, TW::S, TW::R, TW::D}, {TW::Q}, features);
		setup_type(TW($_DFFSR_NNP_), {TW::C, TW::S, TW::R, TW::D}, {TW::Q}, features);
		setup_type(TW($_DFFSR_NPN_), {TW::C, TW::S, TW::R, TW::D}, {TW::Q}, features);
		setup_type(TW($_DFFSR_NPP_), {TW::C, TW::S, TW::R, TW::D}, {TW::Q}, features);
		setup_type(TW($_DFFSR_PNN_), {TW::C, TW::S, TW::R, TW::D}, {TW::Q}, features);
		setup_type(TW($_DFFSR_PNP_), {TW::C, TW::S, TW::R, TW::D}, {TW::Q}, features);
		setup_type(TW($_DFFSR_PPN_), {TW::C, TW::S, TW::R, TW::D}, {TW::Q}, features);
		setup_type(TW($_DFFSR_PPP_), {TW::C, TW::S, TW::R, TW::D}, {TW::Q}, features);
		// for (auto c1 : list_np)
		// for (auto c2 : list_np)
		// for (auto c3 : list_np)
		// for (auto c4 : list_np)
		// 	setup_type(std::string("$_DFFSRE_") + c1 + c2 + c3 + c4 + "_", {TW::C, TW::S, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_DFFSRE_NNNN_), {TW::C, TW::S, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_DFFSRE_NNNP_), {TW::C, TW::S, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_DFFSRE_NNPN_), {TW::C, TW::S, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_DFFSRE_NNPP_), {TW::C, TW::S, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_DFFSRE_NPNN_), {TW::C, TW::S, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_DFFSRE_NPNP_), {TW::C, TW::S, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_DFFSRE_NPPN_), {TW::C, TW::S, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_DFFSRE_NPPP_), {TW::C, TW::S, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_DFFSRE_PNNN_), {TW::C, TW::S, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_DFFSRE_PNNP_), {TW::C, TW::S, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_DFFSRE_PNPN_), {TW::C, TW::S, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_DFFSRE_PNPP_), {TW::C, TW::S, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_DFFSRE_PPNN_), {TW::C, TW::S, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_DFFSRE_PPNP_), {TW::C, TW::S, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_DFFSRE_PPPN_), {TW::C, TW::S, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_DFFSRE_PPPP_), {TW::C, TW::S, TW::R, TW::D, TW::E}, {TW::Q}, features);
		// for (auto c1 : list_np)
		// for (auto c2 : list_np)
		// for (auto c3 : list_01)
		// 	setup_type(std::string("$_SDFF_") + c1 + c2 + c3 + "_", {TW::C, TW::R, TW::D}, {TW::Q}, features);
		setup_type(TW($_SDFF_NN0_), {TW::C, TW::R, TW::D}, {TW::Q}, features);
		setup_type(TW($_SDFF_NN1_), {TW::C, TW::R, TW::D}, {TW::Q}, features);
		setup_type(TW($_SDFF_NP0_), {TW::C, TW::R, TW::D}, {TW::Q}, features);
		setup_type(TW($_SDFF_NP1_), {TW::C, TW::R, TW::D}, {TW::Q}, features);
		setup_type(TW($_SDFF_PN0_), {TW::C, TW::R, TW::D}, {TW::Q}, features);
		setup_type(TW($_SDFF_PN1_), {TW::C, TW::R, TW::D}, {TW::Q}, features);
		setup_type(TW($_SDFF_PP0_), {TW::C, TW::R, TW::D}, {TW::Q}, features);
		setup_type(TW($_SDFF_PP1_), {TW::C, TW::R, TW::D}, {TW::Q}, features);
		// for (auto c1 : list_np)
		// for (auto c2 : list_np)
		// for (auto c3 : list_01)
		// for (auto c4 : list_np)
		// 	setup_type(std::string("$_SDFFE_") + c1 + c2 + c3 + c4 + "_", {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_SDFFE_NN0N_), {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_SDFFE_NN0P_), {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_SDFFE_NN1N_), {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_SDFFE_NN1P_), {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_SDFFE_NP0N_), {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_SDFFE_NP0P_), {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_SDFFE_NP1N_), {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_SDFFE_NP1P_), {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_SDFFE_PN0N_), {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_SDFFE_PN0P_), {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_SDFFE_PN1N_), {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_SDFFE_PN1P_), {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_SDFFE_PP0N_), {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_SDFFE_PP0P_), {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_SDFFE_PP1N_), {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_SDFFE_PP1P_), {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		// for (auto c1 : list_np)
		// for (auto c2 : list_np)
		// for (auto c3 : list_01)
		// for (auto c4 : list_np)
		// 	setup_type(std::string("$_SDFFCE_") + c1 + c2 + c3 + c4 + "_", {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_SDFFCE_NN0N_), {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_SDFFCE_NN0P_), {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_SDFFCE_NN1N_), {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_SDFFCE_NN1P_), {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_SDFFCE_NP0N_), {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_SDFFCE_NP0P_), {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_SDFFCE_NP1N_), {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_SDFFCE_NP1P_), {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_SDFFCE_PN0N_), {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_SDFFCE_PN0P_), {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_SDFFCE_PN1N_), {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_SDFFCE_PN1P_), {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_SDFFCE_PP0N_), {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_SDFFCE_PP0P_), {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_SDFFCE_PP1N_), {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		setup_type(TW($_SDFFCE_PP1P_), {TW::C, TW::R, TW::D, TW::E}, {TW::Q}, features);
		// for (auto c1 : list_np)
		// 	setup_type(std::string("$_DLATCH_") + c1 + "_", {TW::E, TW::D}, {TW::Q}, features);
		setup_type(TW($_DLATCH_N_), {TW::E, TW::D}, {TW::Q}, features);
		setup_type(TW($_DLATCH_P_), {TW::E, TW::D}, {TW::Q}, features);

		// for (auto c1 : list_np)
		// for (auto c2 : list_np)
		// for (auto c3 : list_01)
		// 	setup_type(std::string("$_DLATCH_") + c1 + c2 + c3 + "_", {TW::E, TW::R, TW::D}, {TW::Q}, features);
		setup_type(TW($_DLATCH_NN0_), {TW::E, TW::R, TW::D}, {TW::Q}, features);
		setup_type(TW($_DLATCH_NN1_), {TW::E, TW::R, TW::D}, {TW::Q}, features);
		setup_type(TW($_DLATCH_NP0_), {TW::E, TW::R, TW::D}, {TW::Q}, features);
		setup_type(TW($_DLATCH_NP1_), {TW::E, TW::R, TW::D}, {TW::Q}, features);
		setup_type(TW($_DLATCH_PN0_), {TW::E, TW::R, TW::D}, {TW::Q}, features);
		setup_type(TW($_DLATCH_PN1_), {TW::E, TW::R, TW::D}, {TW::Q}, features);
		setup_type(TW($_DLATCH_PP0_), {TW::E, TW::R, TW::D}, {TW::Q}, features);
		setup_type(TW($_DLATCH_PP1_), {TW::E, TW::R, TW::D}, {TW::Q}, features);
		// for (auto c1 : list_np)
		// for (auto c2 : list_np)
		// for (auto c3 : list_np)
		// 	setup_type(std::string("$_DLATCHSR_") + c1 + c2 + c3 + "_", {TW::E, TW::S, TW::R, TW::D}, {TW::Q}, features);
		setup_type(TW($_DLATCHSR_NNN_), {TW::E, TW::S, TW::R, TW::D}, {TW::Q}, features);
		setup_type(TW($_DLATCHSR_NNP_), {TW::E, TW::S, TW::R, TW::D}, {TW::Q}, features);
		setup_type(TW($_DLATCHSR_NPN_), {TW::E, TW::S, TW::R, TW::D}, {TW::Q}, features);
		setup_type(TW($_DLATCHSR_NPP_), {TW::E, TW::S, TW::R, TW::D}, {TW::Q}, features);
		setup_type(TW($_DLATCHSR_PNN_), {TW::E, TW::S, TW::R, TW::D}, {TW::Q}, features);
		setup_type(TW($_DLATCHSR_PNP_), {TW::E, TW::S, TW::R, TW::D}, {TW::Q}, features);
		setup_type(TW($_DLATCHSR_PPN_), {TW::E, TW::S, TW::R, TW::D}, {TW::Q}, features);
		setup_type(TW($_DLATCHSR_PPP_), {TW::E, TW::S, TW::R, TW::D}, {TW::Q}, features);
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

constexpr CellTableBuilder builder {};

struct PortInfo {
	struct PortLists {
		std::array<CellTableBuilder::PortList, MAX_CELLS> data{};
		constexpr CellTableBuilder::PortList operator()(TwineRef type) const {
			return data[type];
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
			size_t idx = cell.type;
			inputs[idx] = cell.inputs;
			outputs[idx] = cell.outputs;
		}
	}
};

struct Categories {
	struct Category {
		std::array<bool, MAX_CELLS> data{};
		constexpr bool operator()(TwineRef type) const {
			size_t idx = type;
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
		for (size_t i = 0; i < builder.count; ++i) {
			auto& cell = builder.cells[i];
			size_t idx = cell.type;
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
	// old setup_internals + setup_stdcells
	static constexpr auto nomem_noff = Categories::meet(categories.is_known, Categories::complement(mem_ff));
	static constexpr auto internals_mem_ff = Categories::meet(internals_all, mem_ff);
	// old setup_internals
	static constexpr auto internals_nomem_noff = Categories::meet(internals_all, nomem_noff);
	// old setup_stdcells
	static constexpr auto stdcells_nomem_noff = Categories::meet(categories.is_stdcell, nomem_noff);
	static constexpr auto stdcells_mem = Categories::meet(categories.is_stdcell, categories.is_mem_noff);
	// old setup_internals_eval
	// static constexpr auto internals_eval = Categories::meet(internals_all, categories.is_evaluable);
};

namespace {
	static_assert(categories.is_evaluable(TW($and)));
	static_assert(!categories.is_ff(TW($and)));
	static_assert(Categories::join(categories.is_evaluable, categories.is_ff)(TW($and)));
	static_assert(Categories::join(categories.is_evaluable, categories.is_ff)(TW($dffsr)));
	static_assert(!Categories::join(categories.is_evaluable, categories.is_ff)(TW($anyinit)));
}

};

struct NewCellType {
	TwineRef type;
	pool<TwineRef> inputs, outputs;
	bool is_evaluable;
	bool is_combinatorial;
	bool is_synthesizable;
};

struct NewCellTypes {
	StaticCellTypes::Categories::Category static_cell_types = StaticCellTypes::categories.empty;
	dict<TwineRef, NewCellType> custom_cell_types {};

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
		pool<TwineRef> inputs, outputs;
		for (auto wire_name : module->ports) {
			RTLIL::Wire *wire = module->wire(wire_name);
			if (wire->port_input)
				inputs.insert(wire->meta_->name);
			if (wire->port_output)
				outputs.insert(wire->meta_->name);
		}
		setup_type(module->meta_->name, inputs, outputs);
	}

	void setup_type(TwineRef type, const pool<TwineRef> &inputs, const pool<TwineRef> &outputs, bool is_evaluable = false, bool is_combinatorial = false, bool is_synthesizable = false) {
		NewCellType ct = {type, inputs, outputs, is_evaluable, is_combinatorial, is_synthesizable};
		custom_cell_types[ct.type] = ct;
	}

	void clear() {
		custom_cell_types.clear();
		static_cell_types = StaticCellTypes::categories.empty;
	}

	bool cell_known(TwineRef type) const {
		return static_cell_types(type) || custom_cell_types.count(type) != 0;
	}

	bool cell_output(TwineRef type, TwineRef port) const
	{
		// TODO refactor
		if (static_cell_types(type) && StaticCellTypes::port_info.outputs(type).contains(port)) {
			return true;
		}
		auto it = custom_cell_types.find(type);
		return it != custom_cell_types.end() && it->second.outputs.count(port) != 0;
	}

	bool cell_input(TwineRef type, TwineRef port) const
	{
		if (static_cell_types(type) && StaticCellTypes::port_info.inputs(type).contains(port)) {
			return true;
		}
		auto it = custom_cell_types.find(type);
		return it != custom_cell_types.end() && it->second.inputs.count(port) != 0;
	}

	RTLIL::PortDir cell_port_dir(TwineRef type, TwineRef port) const
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
	bool cell_evaluable(TwineRef type) const
	{
		return static_cell_types(type) && StaticCellTypes::categories.is_evaluable(type);
	}
};

extern NewCellTypes yosys_celltypes;

YOSYS_NAMESPACE_END

#endif
