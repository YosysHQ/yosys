#include <gtest/gtest.h>
#include "kernel/yosys.h"
#include "kernel/yosys_common.h"
#include "kernel/celltypes.h"
#include "kernel/newcelltypes.h"

#include <unordered_set>

YOSYS_NAMESPACE_BEGIN

TEST(CellTypesTest, basic)
{
	yosys_setup();
	log_files.push_back(stdout);
	CellTypes older;
	NewCellTypes newer;
	older.setup(nullptr);
	newer.setup(nullptr);
	older.setup_type(ID(bleh), {ID::G}, {ID::H, ID::I}, false, true);
	newer.setup_type(ID(bleh), {ID::G}, {ID::H, ID::I}, false, true);
	EXPECT_EQ(older.cell_known(ID(aaaaa)), newer.cell_known(ID(aaaaa)));
	EXPECT_EQ(older.cell_known(ID($and)), newer.cell_known(ID($and)));
	auto check_port = [&](auto type, auto port) {
		EXPECT_EQ(older.cell_port_dir(type, port), newer.cell_port_dir(type, port));
		EXPECT_EQ(older.cell_input(type, port), newer.cell_input(type, port));
		EXPECT_EQ(older.cell_output(type, port), newer.cell_output(type, port));
	};

	// ground truth
	const pool<IdString> expected_ff_types = {
		ID($sr), ID($ff), ID($dff), ID($dffe), ID($dffsr), ID($dffsre),
		ID($adff), ID($adffe), ID($aldff), ID($aldffe),
		ID($sdff), ID($sdffe), ID($sdffce),
		ID($dlatch), ID($adlatch), ID($dlatchsr),
		ID($_DFFE_NN_), ID($_DFFE_NP_), ID($_DFFE_PN_), ID($_DFFE_PP_),
		ID($_DFFSR_NNN_), ID($_DFFSR_NNP_), ID($_DFFSR_NPN_), ID($_DFFSR_NPP_),
		ID($_DFFSR_PNN_), ID($_DFFSR_PNP_), ID($_DFFSR_PPN_), ID($_DFFSR_PPP_),
		ID($_DFFSRE_NNNN_), ID($_DFFSRE_NNNP_), ID($_DFFSRE_NNPN_), ID($_DFFSRE_NNPP_),
		ID($_DFFSRE_NPNN_), ID($_DFFSRE_NPNP_), ID($_DFFSRE_NPPN_), ID($_DFFSRE_NPPP_),
		ID($_DFFSRE_PNNN_), ID($_DFFSRE_PNNP_), ID($_DFFSRE_PNPN_), ID($_DFFSRE_PNPP_),
		ID($_DFFSRE_PPNN_), ID($_DFFSRE_PPNP_), ID($_DFFSRE_PPPN_), ID($_DFFSRE_PPPP_),
		ID($_DFF_N_), ID($_DFF_P_),
		ID($_DFF_NN0_), ID($_DFF_NN1_), ID($_DFF_NP0_), ID($_DFF_NP1_),
		ID($_DFF_PN0_), ID($_DFF_PN1_), ID($_DFF_PP0_), ID($_DFF_PP1_),
		ID($_DFFE_NN0N_), ID($_DFFE_NN0P_), ID($_DFFE_NN1N_), ID($_DFFE_NN1P_),
		ID($_DFFE_NP0N_), ID($_DFFE_NP0P_), ID($_DFFE_NP1N_), ID($_DFFE_NP1P_),
		ID($_DFFE_PN0N_), ID($_DFFE_PN0P_), ID($_DFFE_PN1N_), ID($_DFFE_PN1P_),
		ID($_DFFE_PP0N_), ID($_DFFE_PP0P_), ID($_DFFE_PP1N_), ID($_DFFE_PP1P_),
		ID($_ALDFF_NN_), ID($_ALDFF_NP_), ID($_ALDFF_PN_), ID($_ALDFF_PP_),
		ID($_ALDFFE_NNN_), ID($_ALDFFE_NNP_), ID($_ALDFFE_NPN_), ID($_ALDFFE_NPP_),
		ID($_ALDFFE_PNN_), ID($_ALDFFE_PNP_), ID($_ALDFFE_PPN_), ID($_ALDFFE_PPP_),
		ID($_SDFF_NN0_), ID($_SDFF_NN1_), ID($_SDFF_NP0_), ID($_SDFF_NP1_),
		ID($_SDFF_PN0_), ID($_SDFF_PN1_), ID($_SDFF_PP0_), ID($_SDFF_PP1_),
		ID($_SDFFE_NN0N_), ID($_SDFFE_NN0P_), ID($_SDFFE_NN1N_), ID($_SDFFE_NN1P_),
		ID($_SDFFE_NP0N_), ID($_SDFFE_NP0P_), ID($_SDFFE_NP1N_), ID($_SDFFE_NP1P_),
		ID($_SDFFE_PN0N_), ID($_SDFFE_PN0P_), ID($_SDFFE_PN1N_), ID($_SDFFE_PN1P_),
		ID($_SDFFE_PP0N_), ID($_SDFFE_PP0P_), ID($_SDFFE_PP1N_), ID($_SDFFE_PP1P_),
		ID($_SDFFCE_NN0N_), ID($_SDFFCE_NN0P_), ID($_SDFFCE_NN1N_), ID($_SDFFCE_NN1P_),
		ID($_SDFFCE_NP0N_), ID($_SDFFCE_NP0P_), ID($_SDFFCE_NP1N_), ID($_SDFFCE_NP1P_),
		ID($_SDFFCE_PN0N_), ID($_SDFFCE_PN0P_), ID($_SDFFCE_PN1N_), ID($_SDFFCE_PN1P_),
		ID($_SDFFCE_PP0N_), ID($_SDFFCE_PP0P_), ID($_SDFFCE_PP1N_), ID($_SDFFCE_PP1P_),
		ID($_SR_NN_), ID($_SR_NP_), ID($_SR_PN_), ID($_SR_PP_),
		ID($_DLATCH_N_), ID($_DLATCH_P_),
		ID($_DLATCH_NN0_), ID($_DLATCH_NN1_), ID($_DLATCH_NP0_), ID($_DLATCH_NP1_),
		ID($_DLATCH_PN0_), ID($_DLATCH_PN1_), ID($_DLATCH_PP0_), ID($_DLATCH_PP1_),
		ID($_DLATCHSR_NNN_), ID($_DLATCHSR_NNP_), ID($_DLATCHSR_NPN_), ID($_DLATCHSR_NPP_),
		ID($_DLATCHSR_PNN_), ID($_DLATCHSR_PNP_), ID($_DLATCHSR_PPN_), ID($_DLATCHSR_PPP_),
		ID($_FF_),
	};

	for (size_t i = 0; i < static_cast<size_t>(RTLIL::StaticId::STATIC_ID_END); i++) {
		IdString type;
		type.index_ = i;
		EXPECT_EQ(older.cell_known(type), newer.cell_known(type));
		if (older.cell_evaluable(type) != newer.cell_evaluable(type))
			std::cout << type.str() << "\n";
		EXPECT_EQ(older.cell_evaluable(type), newer.cell_evaluable(type));
		for (auto port : StaticCellTypes::builder.cells.data()->inputs.ports)
			check_port(type, port);
		for (auto port : StaticCellTypes::builder.cells.data()->outputs.ports)
			check_port(type, port);
		EXPECT_EQ(expected_ff_types.count(type) > 0, StaticCellTypes::categories.is_ff(type));
	}
	yosys_shutdown();
}

YOSYS_NAMESPACE_END
