#include <gtest/gtest.h>
#include "kernel/yosys.h"
#include "kernel/yosys_common.h"
#include "kernel/celltypes.h"
#include "kernel/newcelltypes.h"
#include "tests/unit/yosysSetupEnv.h"

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
	older.setup_type(TW(bleh), {TW::G}, {TW::H, TW::I}, false, true);
	newer.setup_type(TW(bleh), {TW::G}, {TW::H, TW::I}, false, true);
	EXPECT_EQ(older.cell_known(TW(aaaaa)), newer.cell_known(TW(aaaaa)));
	EXPECT_EQ(older.cell_known(TW($and)), newer.cell_known(TW($and)));
	auto check_port = [&](auto type, auto port) {
		EXPECT_EQ(older.cell_port_dir(type, port), newer.cell_port_dir(type, port));
		EXPECT_EQ(older.cell_input(type, port), newer.cell_input(type, port));
		EXPECT_EQ(older.cell_output(type, port), newer.cell_output(type, port));
	};

	// ground truth
	const pool<TwineRef> expected_ff_types = {
		TW($sr), TW($ff), TW($dff), TW($dffe), TW($dffsr), TW($dffsre),
		TW($adff), TW($adffe), TW($aldff), TW($aldffe),
		TW($sdff), TW($sdffe), TW($sdffce),
		TW($dlatch), TW($adlatch), TW($dlatchsr),
		TW($_DFFE_NN_), TW($_DFFE_NP_), TW($_DFFE_PN_), TW($_DFFE_PP_),
		TW($_DFFSR_NNN_), TW($_DFFSR_NNP_), TW($_DFFSR_NPN_), TW($_DFFSR_NPP_),
		TW($_DFFSR_PNN_), TW($_DFFSR_PNP_), TW($_DFFSR_PPN_), TW($_DFFSR_PPP_),
		TW($_DFFSRE_NNNN_), TW($_DFFSRE_NNNP_), TW($_DFFSRE_NNPN_), TW($_DFFSRE_NNPP_),
		TW($_DFFSRE_NPNN_), TW($_DFFSRE_NPNP_), TW($_DFFSRE_NPPN_), TW($_DFFSRE_NPPP_),
		TW($_DFFSRE_PNNN_), TW($_DFFSRE_PNNP_), TW($_DFFSRE_PNPN_), TW($_DFFSRE_PNPP_),
		TW($_DFFSRE_PPNN_), TW($_DFFSRE_PPNP_), TW($_DFFSRE_PPPN_), TW($_DFFSRE_PPPP_),
		TW($_DFF_N_), TW($_DFF_P_),
		TW($_DFF_NN0_), TW($_DFF_NN1_), TW($_DFF_NP0_), TW($_DFF_NP1_),
		TW($_DFF_PN0_), TW($_DFF_PN1_), TW($_DFF_PP0_), TW($_DFF_PP1_),
		TW($_DFFE_NN0N_), TW($_DFFE_NN0P_), TW($_DFFE_NN1N_), TW($_DFFE_NN1P_),
		TW($_DFFE_NP0N_), TW($_DFFE_NP0P_), TW($_DFFE_NP1N_), TW($_DFFE_NP1P_),
		TW($_DFFE_PN0N_), TW($_DFFE_PN0P_), TW($_DFFE_PN1N_), TW($_DFFE_PN1P_),
		TW($_DFFE_PP0N_), TW($_DFFE_PP0P_), TW($_DFFE_PP1N_), TW($_DFFE_PP1P_),
		TW($_ALDFF_NN_), TW($_ALDFF_NP_), TW($_ALDFF_PN_), TW($_ALDFF_PP_),
		TW($_ALDFFE_NNN_), TW($_ALDFFE_NNP_), TW($_ALDFFE_NPN_), TW($_ALDFFE_NPP_),
		TW($_ALDFFE_PNN_), TW($_ALDFFE_PNP_), TW($_ALDFFE_PPN_), TW($_ALDFFE_PPP_),
		TW($_SDFF_NN0_), TW($_SDFF_NN1_), TW($_SDFF_NP0_), TW($_SDFF_NP1_),
		TW($_SDFF_PN0_), TW($_SDFF_PN1_), TW($_SDFF_PP0_), TW($_SDFF_PP1_),
		TW($_SDFFE_NN0N_), TW($_SDFFE_NN0P_), TW($_SDFFE_NN1N_), TW($_SDFFE_NN1P_),
		TW($_SDFFE_NP0N_), TW($_SDFFE_NP0P_), TW($_SDFFE_NP1N_), TW($_SDFFE_NP1P_),
		TW($_SDFFE_PN0N_), TW($_SDFFE_PN0P_), TW($_SDFFE_PN1N_), TW($_SDFFE_PN1P_),
		TW($_SDFFE_PP0N_), TW($_SDFFE_PP0P_), TW($_SDFFE_PP1N_), TW($_SDFFE_PP1P_),
		TW($_SDFFCE_NN0N_), TW($_SDFFCE_NN0P_), TW($_SDFFCE_NN1N_), TW($_SDFFCE_NN1P_),
		TW($_SDFFCE_NP0N_), TW($_SDFFCE_NP0P_), TW($_SDFFCE_NP1N_), TW($_SDFFCE_NP1P_),
		TW($_SDFFCE_PN0N_), TW($_SDFFCE_PN0P_), TW($_SDFFCE_PN1N_), TW($_SDFFCE_PN1P_),
		TW($_SDFFCE_PP0N_), TW($_SDFFCE_PP0P_), TW($_SDFFCE_PP1N_), TW($_SDFFCE_PP1P_),
		TW($_SR_NN_), TW($_SR_NP_), TW($_SR_PN_), TW($_SR_PP_),
		TW($_DLATCH_N_), TW($_DLATCH_P_),
		TW($_DLATCH_NN0_), TW($_DLATCH_NN1_), TW($_DLATCH_NP0_), TW($_DLATCH_NP1_),
		TW($_DLATCH_PN0_), TW($_DLATCH_PN1_), TW($_DLATCH_PP0_), TW($_DLATCH_PP1_),
		TW($_DLATCHSR_NNN_), TW($_DLATCHSR_NNP_), TW($_DLATCHSR_NPN_), TW($_DLATCHSR_NPP_),
		TW($_DLATCHSR_PNN_), TW($_DLATCHSR_PNP_), TW($_DLATCHSR_PPN_), TW($_DLATCHSR_PPP_),
		TW($_FF_),
	};

	TwinePool empty_pool;
	for (size_t i = 0; i < static_cast<size_t>(STATIC_TWINE_END); i++) {
		TwineRef type;
		type = i;
		EXPECT_EQ(older.cell_known(type), newer.cell_known(type));
		if (older.cell_evaluable(type) != newer.cell_evaluable(type))
			std::cout << empty_pool.unescaped_str(type) << "\n";
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
