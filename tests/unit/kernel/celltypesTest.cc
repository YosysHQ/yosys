#include <gtest/gtest.h>
#include "kernel/celltypes.h"
#include "kernel/yosys.h"

YOSYS_NAMESPACE_BEGIN

struct ReferenceCellTypes
{
	CellTypes ct;

	void setup_internals_eval()
	{
		for (auto &t : std::vector<std::string>{
			"$not", "$pos", "$buf", "$neg",
			"$reduce_and", "$reduce_or", "$reduce_xor", "$reduce_xnor",
			"$reduce_bool",
			"$logic_not", "$slice", "$lut", "$sop"})
			ct.setup_type(t, {ID::A}, {ID::Y}, true);
		for (auto &t : std::vector<std::string>{
			"$and", "$or", "$xor", "$xnor",
			"$shl", "$shr", "$sshl", "$sshr", "$shift", "$shiftx",
			"$lt", "$le", "$eq", "$ne", "$eqx", "$nex", "$ge", "$gt",
			"$add", "$sub", "$mul", "$div", "$mod", "$divfloor", "$modfloor",
			"$pow",
			"$logic_and", "$logic_or", "$concat", "$macc",
			"$bweqx"})
			ct.setup_type(t, {ID::A, ID::B}, {ID::Y}, true);
		ct.setup_type(ID($mux), {ID::A, ID::B, ID::S}, {ID::Y}, true);
		ct.setup_type(ID($pmux), {ID::A, ID::B, ID::S}, {ID::Y}, true);
		ct.setup_type(ID($bwmux), {ID::A, ID::B, ID::S}, {ID::Y}, true);
		ct.setup_type(ID($bmux), {ID::A, ID::S}, {ID::Y}, true);
		ct.setup_type(ID($demux), {ID::A, ID::S}, {ID::Y}, true);
		ct.setup_type(ID($lcu), {ID::P, ID::G, ID::CI}, {ID::CO}, true);
		ct.setup_type(ID($alu), {ID::A, ID::B, ID::CI, ID::BI}, {ID::X, ID::Y, ID::CO}, true);
		ct.setup_type(ID($macc_v2), {ID::A, ID::B, ID::C}, {ID::Y}, true);
		ct.setup_type(ID($fa), {ID::A, ID::B, ID::C}, {ID::X, ID::Y}, true);
	}

	void setup_internals()
	{
		setup_internals_eval();
		ct.setup_type(ID($tribuf), {ID::A, ID::EN}, {ID::Y}, true);
		ct.setup_type(ID($assert), {ID::A, ID::EN}, pool<IdString>());
		ct.setup_type(ID($assume), {ID::A, ID::EN}, pool<IdString>());
		ct.setup_type(ID($live), {ID::A, ID::EN}, pool<IdString>());
		ct.setup_type(ID($fair), {ID::A, ID::EN}, pool<IdString>());
		ct.setup_type(ID($cover), {ID::A, ID::EN}, pool<IdString>());
		ct.setup_type(ID($initstate), pool<IdString>(), {ID::Y});
		ct.setup_type(ID($anyconst), pool<IdString>(), {ID::Y});
		ct.setup_type(ID($anyseq), pool<IdString>(), {ID::Y});
		ct.setup_type(ID($allconst), pool<IdString>(), {ID::Y});
		ct.setup_type(ID($allseq), pool<IdString>(), {ID::Y});
		ct.setup_type(ID($equiv), {ID::A, ID::B}, {ID::Y});
		ct.setup_type(ID($specify2), {ID::EN, ID::SRC, ID::DST}, pool<IdString>(), true);
		ct.setup_type(ID($specify3), {ID::EN, ID::SRC, ID::DST, ID::DAT}, pool<IdString>(), true);
		ct.setup_type(ID($specrule), {ID::EN_SRC, ID::EN_DST, ID::SRC, ID::DST}, pool<IdString>(), true);
		ct.setup_type(ID($print), {ID::EN, ID::ARGS, ID::TRG}, pool<IdString>());
		ct.setup_type(ID($check), {ID::A, ID::EN, ID::ARGS, ID::TRG}, pool<IdString>());
		ct.setup_type(ID($set_tag), {ID::A, ID::SET, ID::CLR}, {ID::Y});
		ct.setup_type(ID($get_tag), {ID::A}, {ID::Y});
		ct.setup_type(ID($overwrite_tag), {ID::A, ID::SET, ID::CLR}, pool<IdString>());
		ct.setup_type(ID($original_tag), {ID::A}, {ID::Y});
		ct.setup_type(ID($future_ff), {ID::A}, {ID::Y});
		ct.setup_type(ID($scopeinfo), pool<IdString>(), pool<IdString>());
		ct.setup_type(ID($input_port), pool<IdString>(), {ID::Y});
		ct.setup_type(ID($connect), {ID::A, ID::B}, pool<IdString>());
	}

	void setup_internals_ff()
	{
		ct.setup_type(ID($sr), {ID::SET, ID::CLR}, {ID::Q});
		ct.setup_type(ID($ff), {ID::D}, {ID::Q});
		ct.setup_type(ID($dff), {ID::CLK, ID::D}, {ID::Q});
		ct.setup_type(ID($dffe), {ID::CLK, ID::EN, ID::D}, {ID::Q});
		ct.setup_type(ID($dffsr), {ID::CLK, ID::SET, ID::CLR, ID::D}, {ID::Q});
		ct.setup_type(ID($dffsre), {ID::CLK, ID::SET, ID::CLR, ID::D, ID::EN}, {ID::Q});
		ct.setup_type(ID($adff), {ID::CLK, ID::ARST, ID::D}, {ID::Q});
		ct.setup_type(ID($adffe), {ID::CLK, ID::ARST, ID::D, ID::EN}, {ID::Q});
		ct.setup_type(ID($aldff), {ID::CLK, ID::ALOAD, ID::AD, ID::D}, {ID::Q});
		ct.setup_type(ID($aldffe), {ID::CLK, ID::ALOAD, ID::AD, ID::D, ID::EN}, {ID::Q});
		ct.setup_type(ID($sdff), {ID::CLK, ID::SRST, ID::D}, {ID::Q});
		ct.setup_type(ID($sdffe), {ID::CLK, ID::SRST, ID::D, ID::EN}, {ID::Q});
		ct.setup_type(ID($sdffce), {ID::CLK, ID::SRST, ID::D, ID::EN}, {ID::Q});
		ct.setup_type(ID($dlatch), {ID::EN, ID::D}, {ID::Q});
		ct.setup_type(ID($adlatch), {ID::EN, ID::D, ID::ARST}, {ID::Q});
		ct.setup_type(ID($dlatchsr), {ID::EN, ID::SET, ID::CLR, ID::D}, {ID::Q});
	}

	void setup_internals_anyinit() { ct.setup_type(ID($anyinit), {ID::D}, {ID::Q}); }

	void setup_internals_mem()
	{
		setup_internals_ff();
		ct.setup_type(ID($memrd), {ID::CLK, ID::EN, ID::ADDR}, {ID::DATA});
		ct.setup_type(ID($memrd_v2), {ID::CLK, ID::EN, ID::ARST, ID::SRST, ID::ADDR}, {ID::DATA});
		ct.setup_type(ID($memwr), {ID::CLK, ID::EN, ID::ADDR, ID::DATA}, pool<IdString>());
		ct.setup_type(ID($memwr_v2), {ID::CLK, ID::EN, ID::ADDR, ID::DATA}, pool<IdString>());
		ct.setup_type(ID($meminit), {ID::ADDR, ID::DATA}, pool<IdString>());
		ct.setup_type(ID($meminit_v2), {ID::ADDR, ID::DATA, ID::EN}, pool<IdString>());
		ct.setup_type(ID($mem), {ID::RD_CLK, ID::RD_EN, ID::RD_ADDR, ID::WR_CLK, ID::WR_EN, ID::WR_ADDR, ID::WR_DATA}, {ID::RD_DATA});
		ct.setup_type(ID($mem_v2), {ID::RD_CLK, ID::RD_EN, ID::RD_ARST, ID::RD_SRST, ID::RD_ADDR, ID::WR_CLK, ID::WR_EN, ID::WR_ADDR, ID::WR_DATA}, {ID::RD_DATA});
		ct.setup_type(ID($fsm), {ID::CLK, ID::ARST, ID::CTRL_IN}, {ID::CTRL_OUT});
	}

	void setup_stdcells_eval()
	{
		ct.setup_type(ID($_BUF_), {ID::A}, {ID::Y}, true);
		ct.setup_type(ID($_NOT_), {ID::A}, {ID::Y}, true);
		ct.setup_type(ID($_AND_), {ID::A, ID::B}, {ID::Y}, true);
		ct.setup_type(ID($_NAND_), {ID::A, ID::B}, {ID::Y}, true);
		ct.setup_type(ID($_OR_), {ID::A, ID::B}, {ID::Y}, true);
		ct.setup_type(ID($_NOR_), {ID::A, ID::B}, {ID::Y}, true);
		ct.setup_type(ID($_XOR_), {ID::A, ID::B}, {ID::Y}, true);
		ct.setup_type(ID($_XNOR_), {ID::A, ID::B}, {ID::Y}, true);
		ct.setup_type(ID($_ANDNOT_), {ID::A, ID::B}, {ID::Y}, true);
		ct.setup_type(ID($_ORNOT_), {ID::A, ID::B}, {ID::Y}, true);
		ct.setup_type(ID($_MUX_), {ID::A, ID::B, ID::S}, {ID::Y}, true);
		ct.setup_type(ID($_NMUX_), {ID::A, ID::B, ID::S}, {ID::Y}, true);
		ct.setup_type(ID($_MUX4_), {ID::A, ID::B, ID::C, ID::D, ID::S, ID::T}, {ID::Y}, true);
		ct.setup_type(ID($_MUX8_), {ID::A, ID::B, ID::C, ID::D, ID::E, ID::F, ID::G, ID::H, ID::S, ID::T, ID::U}, {ID::Y}, true);
		ct.setup_type(ID($_MUX16_), {ID::A, ID::B, ID::C, ID::D, ID::E, ID::F, ID::G, ID::H, ID::I, ID::J, ID::K, ID::L, ID::M, ID::N, ID::O, ID::P, ID::S, ID::T, ID::U, ID::V}, {ID::Y}, true);
		ct.setup_type(ID($_AOI3_), {ID::A, ID::B, ID::C}, {ID::Y}, true);
		ct.setup_type(ID($_OAI3_), {ID::A, ID::B, ID::C}, {ID::Y}, true);
		ct.setup_type(ID($_AOI4_), {ID::A, ID::B, ID::C, ID::D}, {ID::Y}, true);
		ct.setup_type(ID($_OAI4_), {ID::A, ID::B, ID::C, ID::D}, {ID::Y}, true);
	}

	void setup_stdcells() {
		setup_stdcells_eval();
		ct.setup_type(ID($_TBUF_), {ID::A, ID::E}, {ID::Y}, true);
	}

	void setup_stdcells_mem()
	{
		std::string NP = "NP", ZO = "01";
		for (auto c1 : NP) for (auto c2 : NP)
			ct.setup_type(stringf("$_SR_%c%c_", c1, c2), {ID::S, ID::R}, {ID::Q});

		ct.setup_type(ID($_FF_), {ID::D}, {ID::Q});
		for (auto c1 : NP)
			ct.setup_type(stringf("$_DFF_%c_", c1), {ID::C, ID::D}, {ID::Q});

		for (auto c1 : NP)
			for (auto c2 : NP)
				ct.setup_type(stringf("$_DFFE_%c%c_", c1, c2), {ID::C, ID::D, ID::E}, {ID::Q});

		for (auto c1 : NP)
			for (auto c2 : NP)
				for (auto c3 : ZO)
					ct.setup_type(stringf("$_DFF_%c%c%c_", c1, c2, c3), {ID::C, ID::R, ID::D}, {ID::Q});

		for (auto c1 : NP)
			for (auto c2 : NP)
				for (auto c3 : ZO)
					for (auto c4 : NP)
						ct.setup_type(stringf("$_DFFE_%c%c%c%c_", c1, c2, c3, c4), {ID::C, ID::R, ID::D, ID::E}, {ID::Q});
		for (auto c1 : NP)
			for (auto c2 : NP)
				ct.setup_type(stringf("$_ALDFF_%c%c_", c1, c2), {ID::C, ID::L, ID::AD, ID::D}, {ID::Q});

		for (auto c1 : NP)
			for (auto c2 : NP)
				for (auto c3 : NP)
					ct.setup_type(stringf("$_ALDFFE_%c%c%c_", c1, c2, c3), {ID::C, ID::L, ID::AD, ID::D, ID::E}, {ID::Q});

		for (auto c1 : NP)
			for (auto c2 : NP)
				for (auto c3 : NP)
					ct.setup_type(stringf("$_DFFSR_%c%c%c_", c1, c2, c3), {ID::C, ID::S, ID::R, ID::D}, {ID::Q});

		for (auto c1 : NP)
			for (auto c2 : NP)
				for (auto c3 : NP)
					for (auto c4 : NP)
						ct.setup_type(stringf("$_DFFSRE_%c%c%c%c_", c1, c2, c3, c4), {ID::C, ID::S, ID::R, ID::D, ID::E}, {ID::Q});

		for (auto c1 : NP)
			for (auto c2 : NP)
				for (auto c3 : ZO)
					ct.setup_type(stringf("$_SDFF_%c%c%c_", c1, c2, c3), {ID::C, ID::R, ID::D}, {ID::Q});

		for (auto c1 : NP)
			for (auto c2 : NP)
				for (auto c3 : ZO)
					for (auto c4 : NP)
						ct.setup_type(stringf("$_SDFFE_%c%c%c%c_", c1, c2, c3, c4), {ID::C, ID::R, ID::D, ID::E}, {ID::Q});

		for (auto c1 : NP)
			for (auto c2 : NP)
				for (auto c3 : ZO)
					for (auto c4 : NP)
						ct.setup_type(stringf("$_SDFFCE_%c%c%c%c_", c1, c2, c3, c4), {ID::C, ID::R, ID::D, ID::E}, {ID::Q});

		for (auto c1 : NP)
			ct.setup_type(stringf("$_DLATCH_%c_", c1), {ID::E, ID::D}, {ID::Q});

		for (auto c1 : NP)
			for (auto c2 : NP)
				for (auto c3 : ZO)
					ct.setup_type(stringf("$_DLATCH_%c%c%c_", c1, c2, c3), {ID::E, ID::R, ID::D}, {ID::Q});

		for (auto c1 : NP)
			for (auto c2 : NP)
				for (auto c3 : NP)
					ct.setup_type(stringf("$_DLATCHSR_%c%c%c_", c1, c2, c3), {ID::E, ID::S, ID::R, ID::D}, {ID::Q});
	}

	void setup() {
		setup_internals();
		setup_internals_mem();
		setup_internals_anyinit();
		setup_stdcells();
		setup_stdcells_mem();
	}
};

static std::vector<IdString> all_cell_type_names() {
	ReferenceCellTypes ref;
	ref.setup();
	std::vector<IdString> n;
	for (auto &it : ref.ct.cell_types)
		n.push_back(it.first);

	std::sort(n.begin(), n.end()); return n;
}

static std::vector<IdString> all_port_names() {
	ReferenceCellTypes ref;
	ref.setup();
	pool<IdString> ports;
	for (auto &it : ref.ct.cell_types) {
		for (auto &p : it.second.inputs)
			ports.insert(p);
		for (auto &p : it.second.outputs)
			ports.insert(p);
	}

	for (auto id : {ID::Y, ID::Q, ID::A, ID::B, ID::D, ID::S, ID::EN, ID::CLK, ID::SET, ID::CLR, ID::ARST, ID::SRST, ID::ALOAD})
		ports.insert(id);

	std::vector<IdString> r(ports.begin(), ports.end()); std::sort(r.begin(), r.end());
	return r;
}

struct SetupScenario { std::string name; std::function<void(ReferenceCellTypes&)> setup_ref; std::function<void(CellTypes&)> setup_dut; };

static void ref_setup_internals_eval(ReferenceCellTypes &r) { r.setup_internals_eval(); }
static void ref_setup_internals(ReferenceCellTypes &r) { r.setup_internals(); }
static void ref_setup_internals_ff(ReferenceCellTypes &r) { r.setup_internals_ff(); }
static void ref_setup_internals_anyinit(ReferenceCellTypes &r) { r.setup_internals_anyinit(); }
static void ref_setup_internals_mem(ReferenceCellTypes &r) { r.setup_internals_mem(); }
static void ref_setup_stdcells_eval(ReferenceCellTypes &r) { r.setup_stdcells_eval(); }
static void ref_setup_stdcells(ReferenceCellTypes &r) { r.setup_stdcells(); }
static void ref_setup_stdcells_mem(ReferenceCellTypes &r) { r.setup_stdcells_mem(); }
static void ref_const_eval(ReferenceCellTypes &r) { r.setup_internals(); r.setup_stdcells(); }
static void ref_int_mem_std(ReferenceCellTypes &r) { r.setup_internals(); r.setup_internals_mem(); r.setup_stdcells(); }
static void ref_full_setup(ReferenceCellTypes &r) { r.setup(); }
static void ref_only_ffs(ReferenceCellTypes &r) { r.setup_internals_ff(); r.setup_stdcells_mem(); }
static void ref_only_eval(ReferenceCellTypes &r) { r.setup_internals_eval(); r.setup_stdcells_eval(); }
static void ref_inc_eval_ff_mem(ReferenceCellTypes &r) { r.setup_internals_eval(); r.setup_internals_ff(); r.setup_internals_mem(); }
static void ref_std_eval_mem(ReferenceCellTypes &r) { r.setup_stdcells_eval(); r.setup_stdcells_mem(); }
static void ref_everything_no_anyinit(ReferenceCellTypes &r) { r.setup_internals(); r.setup_internals_mem(); r.setup_stdcells(); r.setup_stdcells_mem(); }

static void dut_setup_internals_eval(CellTypes &d) { d.setup_internals_eval(); }
static void dut_setup_internals(CellTypes &d) { d.setup_internals(); }
static void dut_setup_internals_ff(CellTypes &d) { d.setup_internals_ff(); }
static void dut_setup_internals_anyinit(CellTypes &d) { d.setup_internals_anyinit(); }
static void dut_setup_internals_mem(CellTypes &d) { d.setup_internals_mem(); }
static void dut_setup_stdcells_eval(CellTypes &d) { d.setup_stdcells_eval(); }
static void dut_setup_stdcells(CellTypes &d) { d.setup_stdcells(); }
static void dut_setup_stdcells_mem(CellTypes &d) { d.setup_stdcells_mem(); }
static void dut_const_eval(CellTypes &d) { d.setup_internals(); d.setup_stdcells(); }
static void dut_int_mem_std(CellTypes &d) { d.setup_internals(); d.setup_internals_mem(); d.setup_stdcells(); }
static void dut_full_setup(CellTypes &d) { d.setup(); }
static void dut_only_ffs(CellTypes &d) { d.setup_internals_ff(); d.setup_stdcells_mem(); }
static void dut_only_eval(CellTypes &d) { d.setup_internals_eval(); d.setup_stdcells_eval(); }
static void dut_inc_eval_ff_mem(CellTypes &d) { d.setup_internals_eval(); d.setup_internals_ff(); d.setup_internals_mem(); }
static void dut_std_eval_mem(CellTypes &d) { d.setup_stdcells_eval(); d.setup_stdcells_mem(); }
static void dut_everything_no_anyinit(CellTypes &d) { d.setup_internals(); d.setup_internals_mem(); d.setup_stdcells(); d.setup_stdcells_mem(); }

static std::vector<SetupScenario> all_scenarios() {
	return {
		{"setup_internals_eval", ref_setup_internals_eval, dut_setup_internals_eval},
		{"setup_internals", ref_setup_internals, dut_setup_internals},
		{"setup_internals_ff", ref_setup_internals_ff, dut_setup_internals_ff},
		{"setup_internals_anyinit", ref_setup_internals_anyinit, dut_setup_internals_anyinit},
		{"setup_internals_mem", ref_setup_internals_mem, dut_setup_internals_mem},
		{"setup_stdcells_eval", ref_setup_stdcells_eval, dut_setup_stdcells_eval},
		{"setup_stdcells", ref_setup_stdcells, dut_setup_stdcells},
		{"setup_stdcells_mem", ref_setup_stdcells_mem, dut_setup_stdcells_mem},
		{"ConstEval pattern", ref_const_eval, dut_const_eval},
		{"internals+mem+stdcells", ref_int_mem_std, dut_int_mem_std},
		{"full setup()", ref_full_setup, dut_full_setup},
		{"only FFs", ref_only_ffs, dut_only_ffs},
		{"only eval", ref_only_eval, dut_only_eval},
		{"incremental: eval+ff+mem", ref_inc_eval_ff_mem, dut_inc_eval_ff_mem},
		{"anyinit alone", ref_setup_internals_anyinit, dut_setup_internals_anyinit},
		{"stdcells_eval+stdcells_mem", ref_std_eval_mem, dut_std_eval_mem},
		{"everything except anyinit", ref_everything_no_anyinit, dut_everything_no_anyinit},
	};
}
class CellTypesTest : public testing::Test {
protected:
	CellTypesTest() { if (log_files.empty()) log_files.emplace_back(stdout); }
	virtual void SetUp() override { IdString::ensure_prepopulated(); }
};

TEST_F(CellTypesTest, MuxPorts)
{
	CellTypes dut;
	dut.setup();
	EXPECT_TRUE(dut.cell_input(ID($mux), ID::A));
	EXPECT_TRUE(dut.cell_input(ID($mux), ID::B));
	EXPECT_TRUE(dut.cell_input(ID($mux), ID::S));
	EXPECT_TRUE(dut.cell_output(ID($mux), ID::Y));
	EXPECT_FALSE(dut.cell_input(ID($mux), ID::Y));
	EXPECT_FALSE(dut.cell_output(ID($mux), ID::A));
}

TEST_F(CellTypesTest, MemCells_CorrectPorts)
{
	CellTypes dut;
	dut.setup();
	EXPECT_TRUE(dut.cell_output(ID($mem), ID::RD_DATA));
	EXPECT_FALSE(dut.cell_output(ID($mem), ID::Y));
	EXPECT_FALSE(dut.cell_output(ID($mem), ID::Q));
	EXPECT_TRUE(dut.cell_output(ID($mem_v2), ID::RD_DATA));
	EXPECT_TRUE(dut.cell_input(ID($mem_v2), ID::WR_DATA));
	EXPECT_TRUE(dut.cell_input(ID($mem_v2), ID::RD_ADDR));
}

TEST_F(CellTypesTest, MemrdPorts)
{
	CellTypes dut;
	dut.setup();
	EXPECT_TRUE(dut.cell_input(ID($memrd), ID::ADDR));
	EXPECT_TRUE(dut.cell_input(ID($memrd), ID::EN));
	EXPECT_TRUE(dut.cell_input(ID($memrd), ID::CLK));
	EXPECT_TRUE(dut.cell_output(ID($memrd), ID::DATA));
	EXPECT_FALSE(dut.cell_output(ID($memrd), ID::Y));
}

TEST_F(CellTypesTest, FsmPorts)
{
	CellTypes dut;
	dut.setup();
	EXPECT_TRUE(dut.cell_input(ID($fsm), ID::CLK));
	EXPECT_TRUE(dut.cell_input(ID($fsm), ID::ARST));
	EXPECT_TRUE(dut.cell_input(ID($fsm), ID::CTRL_IN));
	EXPECT_TRUE(dut.cell_output(ID($fsm), ID::CTRL_OUT));
	EXPECT_FALSE(dut.cell_output(ID($fsm), ID::Y));
}

TEST_F(CellTypesTest, TribufPorts)
{
	CellTypes dut;
	dut.setup();
	EXPECT_TRUE(dut.cell_input(ID($tribuf), ID::A));
	EXPECT_TRUE(dut.cell_input(ID($tribuf), ID::EN));
	EXPECT_TRUE(dut.cell_output(ID($tribuf), ID::Y));
	EXPECT_FALSE(dut.cell_output(ID($tribuf), ID::Q));
}

TEST_F(CellTypesTest, TbufPorts)
{
	CellTypes dut;
	dut.setup();
	EXPECT_TRUE(dut.cell_input(ID($_TBUF_), ID::A));
	EXPECT_TRUE(dut.cell_input(ID($_TBUF_), ID::E));
	EXPECT_TRUE(dut.cell_output(ID($_TBUF_), ID::Y));
}

TEST_F(CellTypesTest, SpecifyPorts)
{
	CellTypes dut;
	dut.setup();
	EXPECT_TRUE(dut.cell_input(ID($specify2), ID::EN));
	EXPECT_TRUE(dut.cell_input(ID($specify2), ID::SRC));
	EXPECT_TRUE(dut.cell_input(ID($specify2), ID::DST));
	EXPECT_FALSE(dut.cell_output(ID($specify2), ID::Y));
	EXPECT_TRUE(dut.cell_input(ID($specify3), ID::DAT));
	EXPECT_TRUE(dut.cell_input(ID($specrule), ID::EN_SRC));
	EXPECT_TRUE(dut.cell_input(ID($specrule), ID::EN_DST));
}

TEST_F(CellTypesTest, CellsWithNoOutputs)
{
	CellTypes dut;
	dut.setup();
	auto ports = all_port_names();
	for (auto &id : {ID($assert), ID($assume), ID($live), ID($fair), ID($cover),
			ID($memwr), ID($memwr_v2), ID($meminit), ID($meminit_v2),
			ID($print), ID($check), ID($overwrite_tag), ID($connect)}) {
		EXPECT_TRUE(dut.cell_known(id)) << id.c_str();
		bool has_output = false;
		for (auto &p : ports)
			if (dut.cell_output(id, p))
				has_output = true;

		EXPECT_FALSE(has_output) << id.c_str() << " should have no outputs";
	}
}

TEST_F(CellTypesTest, CellsWithNoInputs)
{
	CellTypes dut;
	dut.setup();
	auto ports = all_port_names();
	for (auto &id : {ID($initstate), ID($anyconst), ID($anyseq),
			ID($allconst), ID($allseq), ID($scopeinfo), ID($input_port)}) {
		EXPECT_TRUE(dut.cell_known(id)) << id.c_str();
		bool has_input = false;
		for (auto &p : ports)
			if (dut.cell_input(id, p))
				has_input = true;

		EXPECT_FALSE(has_input) << id.c_str() << " should have no inputs";
	}
}

TEST_F(CellTypesTest, ScopeinfoHasNoPorts)
{
	CellTypes dut;
	dut.setup();
	EXPECT_TRUE(dut.cell_known(ID($scopeinfo)));
	EXPECT_FALSE(dut.cell_input(ID($scopeinfo), ID::A));
	EXPECT_FALSE(dut.cell_output(ID($scopeinfo), ID::Y));
}

TEST_F(CellTypesTest, InternalFFs_HaveQ_NotY)
{
	CellTypes dut;
	dut.setup();
	for (auto &type : {ID($sr), ID($ff), ID($dff), ID($dffe), ID($dffsr), ID($dffsre),
			ID($adff), ID($adffe), ID($aldff), ID($aldffe),
			ID($sdff), ID($sdffe), ID($sdffce),
			ID($dlatch), ID($adlatch), ID($dlatchsr)}) {
		SCOPED_TRACE(std::string("cell: ") + type.c_str());
		EXPECT_TRUE(dut.cell_known(type));
		EXPECT_TRUE(dut.cell_output(type, ID::Q));
		EXPECT_FALSE(dut.cell_output(type, ID::Y));
	}
}

TEST_F(CellTypesTest, StdcellFFs_HaveQ_NotY)
{
	CellTypes dut;
	dut.setup();
	ReferenceCellTypes ref;
	ref.setup_stdcells_mem();
	for (auto &it : ref.ct.cell_types) {
		SCOPED_TRACE(std::string("cell: ") + it.first.c_str());
		EXPECT_TRUE(dut.cell_known(it.first));
		EXPECT_TRUE(dut.cell_output(it.first, ID::Q));
		EXPECT_FALSE(dut.cell_output(it.first, ID::Y));
	}
}

TEST_F(CellTypesTest, AnyinitHasQ_NotY)
{
	CellTypes dut;
	dut.setup();
	EXPECT_TRUE(dut.cell_output(ID($anyinit), ID::Q));
	EXPECT_FALSE(dut.cell_output(ID($anyinit), ID::Y));
	EXPECT_TRUE(dut.cell_input(ID($anyinit), ID::D));
}

TEST_F(CellTypesTest, PortDirConsistency)
{
	CellTypes dut;
	dut.setup();
	auto cell_names = all_cell_type_names();
	auto ports = all_port_names();
	for (auto &type : cell_names) {
		if (!dut.cell_known(type))
			continue;
		for (auto &port : ports) {
			auto dir = dut.cell_port_dir(type, port);
			bool is_in  = dut.cell_input(type, port);
			bool is_out = dut.cell_output(type, port);
			auto expected = RTLIL::PortDir((int)is_in + (int)is_out * 2);
			EXPECT_EQ(dir, expected) << type.c_str() << " port " << port.c_str();
		}
	}
}

TEST_F(CellTypesTest, PortDirUnknownCell)
{
	CellTypes dut;
	dut.setup();
	EXPECT_EQ(dut.cell_port_dir(IdString("$fake_cell"), ID::A), RTLIL::PD_UNKNOWN);
}

TEST_F(CellTypesTest, IdempotentSetup)
{
	auto cell_names = all_cell_type_names();
	CellTypes dut1;
	dut1.setup_internals();
	dut1.setup_stdcells();
	CellTypes dut2;
	dut2.setup_internals();
	dut2.setup_stdcells();
	dut2.setup_internals();
	dut2.setup_stdcells();
	for (auto &type : cell_names) {
		EXPECT_EQ(dut1.cell_known(type), dut2.cell_known(type)) << type.c_str();
		EXPECT_EQ(dut1.cell_evaluable(type), dut2.cell_evaluable(type)) << type.c_str();
	}
}

//TEST_F(CellTypesTest, IncrementalSetupAddsCategories)
//{
//	CellTypes dut;
//	dut.setup_internals_eval();
//	EXPECT_TRUE(dut.cell_known(ID($add)));
//	EXPECT_FALSE(dut.cell_known(ID($dff)));
//	EXPECT_FALSE(dut.cell_known(ID($tribuf)));
//	dut.setup_internals();
//	EXPECT_TRUE(dut.cell_known(ID($add)));
//	EXPECT_FALSE(dut.cell_known(ID($dff)));
//	EXPECT_TRUE(dut.cell_known(ID($tribuf)));
//	dut.setup_internals_mem();
//	EXPECT_TRUE(dut.cell_known(ID($add)));
//	EXPECT_TRUE(dut.cell_known(ID($dff)));
//	EXPECT_TRUE(dut.cell_known(ID($tribuf)));
//	EXPECT_TRUE(dut.cell_known(ID($memrd)));
//}

//TEST_F(CellTypesTest, IncrementalSetupStdcells)
//{
//	CellTypes dut;
//	dut.setup_stdcells_eval();
//	EXPECT_TRUE(dut.cell_known(ID($_AND_)));
//	EXPECT_FALSE(dut.cell_known(ID($_TBUF_)));
//	EXPECT_FALSE(dut.cell_known(ID($_FF_)));
//	dut.setup_stdcells();
//	EXPECT_TRUE(dut.cell_known(ID($_AND_)));
//	EXPECT_TRUE(dut.cell_known(ID($_TBUF_)));
//	EXPECT_FALSE(dut.cell_known(ID($_FF_)));
//	dut.setup_stdcells_mem();
//	EXPECT_TRUE(dut.cell_known(ID($_AND_)));
//	EXPECT_TRUE(dut.cell_known(ID($_TBUF_)));
//	EXPECT_TRUE(dut.cell_known(ID($_FF_)));
//}

TEST_F(CellTypesTest, CustomCellsAlongsideBuiltins)
{
	CellTypes dut;
	dut.setup();
	IdString custom_id("$my_custom_cell");
	dut.setup_type(custom_id, {ID::A, ID::B}, {ID::Y}, true);
	EXPECT_TRUE(dut.cell_known(custom_id));
	EXPECT_TRUE(dut.cell_output(custom_id, ID::Y));
	EXPECT_TRUE(dut.cell_input(custom_id, ID::A));
	EXPECT_TRUE(dut.cell_evaluable(custom_id));
	EXPECT_TRUE(dut.cell_known(ID($add)));
	EXPECT_TRUE(dut.cell_known(ID($dff)));
}

TEST_F(CellTypesTest, CustomCellOverridesBuiltin)
{
	CellTypes dut;
	dut.setup();
	dut.setup_type(ID($add), {ID::A}, {ID::Q}, false);
	EXPECT_TRUE(dut.cell_known(ID($add)));
}

TEST_F(CellTypesTest, BitmaskConstants)
{
	EXPECT_EQ(CellTypes::BITS_ALL,
		CellTypes::BIT_INTERNALS_OTHER | CellTypes::BIT_INTERNALS_EVAL |
		CellTypes::BIT_INTERNALS_FF | CellTypes::BIT_INTERNALS_ANYINIT |
		CellTypes::BIT_INTERNALS_MEM | CellTypes::BIT_STDCELLS_EVAL |
		CellTypes::BIT_STDCELLS_TRISTATE | CellTypes::BIT_STDCELLS_FF);
	EXPECT_EQ(CellTypes::BIT_INTERNALS_OTHER,   0x0001);
	EXPECT_EQ(CellTypes::BIT_INTERNALS_EVAL,    0x0002);
	EXPECT_EQ(CellTypes::BIT_INTERNALS_FF,      0x0004);
	EXPECT_EQ(CellTypes::BIT_INTERNALS_ANYINIT, 0x0008);
	EXPECT_EQ(CellTypes::BIT_INTERNALS_MEM,     0x0010);
	EXPECT_EQ(CellTypes::BIT_STDCELLS_EVAL,     0x0020);
	EXPECT_EQ(CellTypes::BIT_STDCELLS_TRISTATE,  0x0040);
	EXPECT_EQ(CellTypes::BIT_STDCELLS_FF,       0x0080);
	EXPECT_EQ(CellTypes::BITS_ALL,              0x00FF);
}

TEST_F(CellTypesTest, EnabledCatsStartsAtZero)
{
	CellTypes dut;
	EXPECT_EQ(dut.enabled_cats, 0);
}

TEST_F(CellTypesTest, SetupMethodsSetsCorrectBits)
{
	{
		CellTypes dut;
		dut.setup_internals_eval();
		EXPECT_TRUE(dut.enabled_cats & CellTypes::BIT_INTERNALS_EVAL);
		EXPECT_FALSE(dut.enabled_cats & CellTypes::BIT_INTERNALS_OTHER);
		EXPECT_FALSE(dut.enabled_cats & CellTypes::BIT_INTERNALS_FF);
	}
	{
		CellTypes dut;
		dut.setup_internals();
		EXPECT_TRUE(dut.enabled_cats & CellTypes::BIT_INTERNALS_EVAL);
		EXPECT_TRUE(dut.enabled_cats & CellTypes::BIT_INTERNALS_OTHER);
		EXPECT_FALSE(dut.enabled_cats & CellTypes::BIT_INTERNALS_FF);
		EXPECT_FALSE(dut.enabled_cats & CellTypes::BIT_INTERNALS_MEM);
		EXPECT_FALSE(dut.enabled_cats & CellTypes::BIT_INTERNALS_ANYINIT);
	}
	{
		CellTypes dut;
		dut.setup_internals_ff();
		EXPECT_TRUE(dut.enabled_cats & CellTypes::BIT_INTERNALS_FF);
		EXPECT_FALSE(dut.enabled_cats & CellTypes::BIT_INTERNALS_EVAL);
	}
	{
		CellTypes dut;
		dut.setup_internals_mem();
		EXPECT_TRUE(dut.enabled_cats & CellTypes::BIT_INTERNALS_FF);
		EXPECT_TRUE(dut.enabled_cats & CellTypes::BIT_INTERNALS_MEM);
	}
	{
		CellTypes dut;
		dut.setup_internals_anyinit();
		EXPECT_TRUE(dut.enabled_cats & CellTypes::BIT_INTERNALS_ANYINIT);
		EXPECT_EQ(dut.enabled_cats, CellTypes::BIT_INTERNALS_ANYINIT);
	}
	{
		CellTypes dut;
		dut.setup_stdcells_eval();
		EXPECT_TRUE(dut.enabled_cats & CellTypes::BIT_STDCELLS_EVAL);
		EXPECT_FALSE(dut.enabled_cats & CellTypes::BIT_STDCELLS_TRISTATE);
		EXPECT_FALSE(dut.enabled_cats & CellTypes::BIT_STDCELLS_FF);
	}
	{
		CellTypes dut;
		dut.setup_stdcells();
		EXPECT_TRUE(dut.enabled_cats & CellTypes::BIT_STDCELLS_EVAL);
		EXPECT_TRUE(dut.enabled_cats & CellTypes::BIT_STDCELLS_TRISTATE);
		EXPECT_FALSE(dut.enabled_cats & CellTypes::BIT_STDCELLS_FF);
	}
	{
		CellTypes dut;
		dut.setup_stdcells_mem();
		EXPECT_TRUE(dut.enabled_cats & CellTypes::BIT_STDCELLS_FF);
		EXPECT_FALSE(dut.enabled_cats & CellTypes::BIT_STDCELLS_EVAL);
	}
	{
		CellTypes dut;
		dut.setup();
		EXPECT_EQ(dut.enabled_cats, CellTypes::BITS_ALL);
	}
}

TEST_F(CellTypesTest, Mux16Ports)
{
	CellTypes dut;
	dut.setup();
	for (auto &id : {ID::A, ID::B, ID::C, ID::D, ID::E, ID::F, ID::G, ID::H,
			ID::I, ID::J, ID::K, ID::L, ID::M, ID::N, ID::O, ID::P,
			ID::S, ID::T, ID::U, ID::V})
		EXPECT_TRUE(dut.cell_input(ID($_MUX16_), id)) << id.c_str();
	EXPECT_TRUE(dut.cell_output(ID($_MUX16_), ID::Y));
	EXPECT_FALSE(dut.cell_output(ID($_MUX16_), ID::Q));
}

TEST_F(CellTypesTest, Mux8Ports)
{
	CellTypes dut;
	dut.setup();
	for (auto &id : {ID::A, ID::B, ID::C, ID::D, ID::E, ID::F, ID::G, ID::H,
			ID::S, ID::T, ID::U})
		EXPECT_TRUE(dut.cell_input(ID($_MUX8_), id)) << id.c_str();
	EXPECT_TRUE(dut.cell_output(ID($_MUX8_), ID::Y));
}

TEST_F(CellTypesTest, StdcellDffVariants)
{
	CellTypes dut;
	dut.setup();
	for (auto &name : {"$_DFF_P_", "$_DFF_N_"}) {
		EXPECT_TRUE(dut.cell_known(IdString(name))) << name;
		EXPECT_TRUE(dut.cell_input(IdString(name), ID::C));
		EXPECT_TRUE(dut.cell_input(IdString(name), ID::D));
		EXPECT_TRUE(dut.cell_output(IdString(name), ID::Q));
	}
	for (auto &name : {"$_DFFE_PP_", "$_DFFE_PN_", "$_DFFE_NP_", "$_DFFE_NN_"}) {
		EXPECT_TRUE(dut.cell_known(IdString(name))) << name;
		EXPECT_TRUE(dut.cell_input(IdString(name), ID::E));
	}
}

TEST_F(CellTypesTest, StdcellDffResetVariants)
{
	CellTypes dut;
	dut.setup();
	for (auto &name : {"$_DFF_PP0_", "$_DFF_PP1_", "$_DFF_PN0_", "$_DFF_PN1_",
			"$_DFF_NP0_", "$_DFF_NP1_", "$_DFF_NN0_", "$_DFF_NN1_"}) {
		EXPECT_TRUE(dut.cell_known(IdString(name))) << name;
		EXPECT_TRUE(dut.cell_input(IdString(name), ID::R));
	}
}

TEST_F(CellTypesTest, StdcellLatchVariants)
{
	CellTypes dut;
	dut.setup();
	EXPECT_TRUE(dut.cell_known(ID($_DLATCH_P_)));
	EXPECT_TRUE(dut.cell_known(ID($_DLATCH_N_)));
	EXPECT_TRUE(dut.cell_input(ID($_DLATCH_P_), ID::E));
	EXPECT_TRUE(dut.cell_input(ID($_DLATCH_P_), ID::D));
	EXPECT_TRUE(dut.cell_output(ID($_DLATCH_P_), ID::Q));
}

TEST_F(CellTypesTest, StdcellSrVariants)
{
	CellTypes dut;
	dut.setup();
	for (auto &name : {"$_SR_PP_", "$_SR_PN_", "$_SR_NP_", "$_SR_NN_"}) {
		EXPECT_TRUE(dut.cell_known(IdString(name))) << name;
		EXPECT_TRUE(dut.cell_input(IdString(name), ID::S));
		EXPECT_TRUE(dut.cell_input(IdString(name), ID::R));
		EXPECT_TRUE(dut.cell_output(IdString(name), ID::Q));
	}
}

TEST_F(CellTypesTest, FastPathEquivalence)
{
	auto cell_names = all_cell_type_names();
	auto ports = all_port_names();

	CellTypes fast;
	fast.setup();
	EXPECT_EQ(fast.enabled_cats, CellTypes::BITS_ALL);

	CellTypes manual;
	manual.setup_internals_eval();
	manual.setup_internals();
	manual.setup_internals_ff();
	manual.setup_internals_anyinit();
	manual.setup_internals_mem();
	manual.setup_stdcells_eval();
	manual.setup_stdcells();
	manual.setup_stdcells_mem();
	EXPECT_EQ(manual.enabled_cats, CellTypes::BITS_ALL);

	for (auto &type : cell_names) {
		EXPECT_EQ(fast.cell_known(type), manual.cell_known(type)) << type.c_str();
		EXPECT_EQ(fast.cell_evaluable(type), manual.cell_evaluable(type)) << type.c_str();
		for (auto &port : ports) {
			EXPECT_EQ(fast.cell_output(type, port), manual.cell_output(type, port))
				<< type.c_str() << " " << port.c_str();
			EXPECT_EQ(fast.cell_input(type, port), manual.cell_input(type, port))
				<< type.c_str() << " " << port.c_str();
		}
	}
}

//TEST_F(CellTypesTest, CellKnown_AllScenarios)
//{
//	auto cn = all_cell_type_names();
//	for (auto &sc : all_scenarios()) {
//		SCOPED_TRACE("scenario: " + sc.name);
//		ReferenceCellTypes ref;
//		sc.setup_ref(ref);
//		CellTypes dut;
//		sc.setup_dut(dut);
//		for (auto &t : cn) {
//			EXPECT_EQ(ref.ct.cell_known(t), dut.cell_known(t)) << t.c_str();
//		}
//	}
//}

//TEST_F(CellTypesTest, CellOutput_AllScenarios)
//{
//	auto cn = all_cell_type_names();
//	auto pp = all_port_names();
//	for (auto &sc : all_scenarios()) {
//		SCOPED_TRACE("scenario: " + sc.name);
//		ReferenceCellTypes ref;
//		sc.setup_ref(ref);
//		CellTypes dut;
//		sc.setup_dut(dut);
//		for (auto &t : cn) {
//			for (auto &p : pp) {
//				EXPECT_EQ(ref.ct.cell_output(t, p), dut.cell_output(t, p)) << t.c_str() << " " << p.c_str();
//			}
//		}
//	}
//}

//TEST_F(CellTypesTest, CellInput_AllScenarios)
//{
//	auto cn = all_cell_type_names();
//	auto pp = all_port_names();
//	for (auto &sc : all_scenarios()) {
//		SCOPED_TRACE("scenario: " + sc.name);
//		ReferenceCellTypes ref;
//		sc.setup_ref(ref);
//		CellTypes dut;
//		sc.setup_dut(dut);
//		for (auto &t : cn) {
//			for (auto &p : pp) {
//				EXPECT_EQ(ref.ct.cell_input(t, p), dut.cell_input(t, p)) << t.c_str() << " " << p.c_str();
//			}
//		}
//	}
//}

// TEST_F(CellTypesTest, CellEvaluable_AllScenarios)
// {
// 	auto cn = all_cell_type_names();
// 	for (auto &sc : all_scenarios()) {
// 		SCOPED_TRACE("scenario: " + sc.name);
// 		ReferenceCellTypes ref;
// 		sc.setup_ref(ref);
// 		CellTypes dut;
// 		sc.setup_dut(dut);
// 		for (auto &t : cn) {
// 			EXPECT_EQ(ref.ct.cell_evaluable(t), dut.cell_evaluable(t)) << t.c_str();
// 		}
// 	}
// }

//TEST_F(CellTypesTest, CellPortDir_AllScenarios)
//{
//	auto cn = all_cell_type_names();
//	auto pp = all_port_names();
//	for (auto &sc : all_scenarios()) {
//		SCOPED_TRACE("scenario: " + sc.name);
//		ReferenceCellTypes ref;
//		sc.setup_ref(ref);
//		CellTypes dut;
//		sc.setup_dut(dut);
//		for (auto &t : cn) {
//			for (auto &p : pp) {
//				EXPECT_EQ(ref.ct.cell_port_dir(t, p), dut.cell_port_dir(t, p)) << t.c_str() << " " << p.c_str();
//			}
//		}
//	}
//}

//TEST_F(CellTypesTest, CellCount_MatchesReference)
//{
//	auto cn = all_cell_type_names();
//	for (auto &sc : all_scenarios()) {
//		SCOPED_TRACE("scenario: " + sc.name);
//		ReferenceCellTypes ref;
//		sc.setup_ref(ref);
//		CellTypes dut;
//		sc.setup_dut(dut);
//		int rc = 0, dc = 0;
//		for (auto &t : cn) {
//			if (ref.ct.cell_known(t)) rc++;
//			if (dut.cell_known(t)) dc++;
//		}
//		EXPECT_EQ(rc, dc);
//	}
//}

TEST_F(CellTypesTest, UnknownCells_NotKnown)
{
	std::vector<IdString> nc = {
		ID($bogus_cell), IdString("$fake"), IdString("$_FAKE_"),
		ID::A, ID::B, ID::Y, ID::Q, ID::WIDTH
	};
	for (auto &sc : all_scenarios()) {
		SCOPED_TRACE("scenario: " + sc.name);
		CellTypes dut;
		sc.setup_dut(dut);
		for (auto &id : nc) {
			EXPECT_FALSE(dut.cell_known(id)) << id.c_str();
		}
	}
}

TEST_F(CellTypesTest, EmptyKnowsNothing)
{
	CellTypes dut;
	for (auto &t : all_cell_type_names()) {
		EXPECT_FALSE(dut.cell_known(t)) << t.c_str();
	}
}

TEST_F(CellTypesTest, ClearResetsState)
{
	CellTypes dut;
	dut.setup();
	EXPECT_TRUE(dut.cell_known(ID($add)));
	EXPECT_TRUE(dut.cell_known(ID($dff)));
	EXPECT_TRUE(dut.cell_known(ID($_AND_)));
	dut.clear();
	EXPECT_FALSE(dut.cell_known(ID($add)));
	EXPECT_FALSE(dut.cell_known(ID($dff)));
	EXPECT_FALSE(dut.cell_known(ID($_AND_)));
}

TEST_F(CellTypesTest, ClearThenResetup)
{
	CellTypes dut;
	dut.setup();
	dut.clear();
	dut.setup_internals_eval();
	EXPECT_TRUE(dut.cell_known(ID($add)));
	EXPECT_FALSE(dut.cell_known(ID($dff)));
	EXPECT_FALSE(dut.cell_known(ID($_AND_)));
}

TEST_F(CellTypesTest, ConstEvalPattern_NoFFs)
{
	CellTypes dut;
	dut.setup_internals();
	dut.setup_stdcells();
	EXPECT_FALSE(dut.cell_known(ID($dff)));
	EXPECT_FALSE(dut.cell_known(ID($ff)));
	EXPECT_FALSE(dut.cell_known(ID($adff)));
	EXPECT_FALSE(dut.cell_known(ID($sr)));
	EXPECT_FALSE(dut.cell_known(ID($dlatch)));
	EXPECT_FALSE(dut.cell_known(ID($memrd)));
	EXPECT_FALSE(dut.cell_known(ID($mem)));
	EXPECT_FALSE(dut.cell_known(ID($fsm)));
	EXPECT_FALSE(dut.cell_known(ID($anyinit)));
	EXPECT_FALSE(dut.cell_known(ID($_FF_)));
	EXPECT_FALSE(dut.cell_known(ID($_DFF_P_)));
	EXPECT_FALSE(dut.cell_known(ID($_SR_PP_)));
	EXPECT_TRUE(dut.cell_known(ID($add)));
	EXPECT_TRUE(dut.cell_known(ID($mux)));
	EXPECT_TRUE(dut.cell_known(ID($_AND_)));
	EXPECT_TRUE(dut.cell_known(ID($tribuf)));
	EXPECT_TRUE(dut.cell_known(ID($assert)));
	EXPECT_TRUE(dut.cell_known(ID($_TBUF_)));
}

//TEST_F(CellTypesTest, EvalOnlyExcludes_OtherCells)
//{
//	CellTypes dut;
//	dut.setup_internals_eval();
//	EXPECT_TRUE(dut.cell_known(ID($add)));
//	EXPECT_FALSE(dut.cell_known(ID($tribuf)));
//	EXPECT_FALSE(dut.cell_known(ID($assert)));
//	EXPECT_FALSE(dut.cell_known(ID($specify2)));
//	EXPECT_FALSE(dut.cell_known(ID($scopeinfo)));
//}

//TEST_F(CellTypesTest, StdcellEvalOnlyExcludes_TBUF)
//{
//	CellTypes dut;
//	dut.setup_stdcells_eval();
//	EXPECT_TRUE(dut.cell_known(ID($_AND_)));
//	EXPECT_FALSE(dut.cell_known(ID($_TBUF_)));
//	EXPECT_FALSE(dut.cell_known(ID($_FF_)));
//}

TEST_F(CellTypesTest, FFOnlyDoesNotKnowEvalCells)
{
	CellTypes dut;
	dut.setup_internals_ff();
	EXPECT_TRUE(dut.cell_known(ID($dff)));
	EXPECT_FALSE(dut.cell_known(ID($add)));
	EXPECT_FALSE(dut.cell_known(ID($_AND_)));
}

TEST_F(CellTypesTest, AnyinitOnlyDoesNotKnowAnythingElse)
{
	CellTypes dut;
	dut.setup_internals_anyinit();
	EXPECT_TRUE(dut.cell_known(ID($anyinit)));
	EXPECT_FALSE(dut.cell_known(ID($dff)));
	EXPECT_FALSE(dut.cell_known(ID($add)));
	EXPECT_FALSE(dut.cell_known(ID($memrd)));
}

TEST_F(CellTypesTest, StdcellMemDoesNotKnowInternalFFs)
{
	CellTypes dut;
	dut.setup_stdcells_mem();
	EXPECT_TRUE(dut.cell_known(ID($_FF_)));
	EXPECT_FALSE(dut.cell_known(ID($dff)));
	EXPECT_FALSE(dut.cell_known(ID($add)));
}

TEST_F(CellTypesTest, InternalFFDoesNotKnowStdcellFF)
{
	CellTypes dut;
	dut.setup_internals_ff();
	EXPECT_TRUE(dut.cell_known(ID($dff)));
	EXPECT_FALSE(dut.cell_known(ID($_DFF_P_)));
}

TEST_F(CellTypesTest, FullSetup_AllKnown)
{
	CellTypes dut;
	dut.setup();
	for (auto &t : all_cell_type_names()) {
		EXPECT_TRUE(dut.cell_known(t)) << t.c_str();
	}
}

TEST_F(CellTypesTest, TribufEvaluable)
{
	CellTypes dut;
	dut.setup();
	EXPECT_TRUE(dut.cell_evaluable(ID($tribuf)));
}

TEST_F(CellTypesTest, SpecifyCellsEvaluable)
{
	CellTypes dut;
	dut.setup();
	EXPECT_TRUE(dut.cell_evaluable(ID($specify2)));
	EXPECT_TRUE(dut.cell_evaluable(ID($specify3)));
	EXPECT_TRUE(dut.cell_evaluable(ID($specrule)));
}

TEST_F(CellTypesTest, TbufEvaluable)
{
	CellTypes dut;
	dut.setup();
	EXPECT_TRUE(dut.cell_evaluable(ID($_TBUF_)));
}

TEST_F(CellTypesTest, FFsNotEvaluable)
{
	CellTypes dut;
	dut.setup();
	for (auto &id : {ID($dff), ID($ff), ID($adff), ID($sdff), ID($sr), ID($dlatch)}) {
		EXPECT_TRUE(dut.cell_known(id)) << id.c_str();
		EXPECT_FALSE(dut.cell_evaluable(id)) << id.c_str();
	}
}

TEST_F(CellTypesTest, StdcellFFsNotEvaluable)
{
	CellTypes dut;
	dut.setup();
	for (auto &id : {ID($_FF_), ID($_DFF_P_), ID($_DFFE_PP_), ID($_DLATCH_P_), ID($_SR_PP_)}) {
		EXPECT_TRUE(dut.cell_known(id)) << id.c_str();
		EXPECT_FALSE(dut.cell_evaluable(id)) << id.c_str();
	}
}

TEST_F(CellTypesTest, MemCellsNotEvaluable)
{
	CellTypes dut;
	dut.setup();
	for (auto &id : {ID($memrd), ID($memrd_v2), ID($memwr), ID($memwr_v2), ID($meminit), ID($meminit_v2), ID($mem), ID($mem_v2), ID($fsm)}) {
		EXPECT_TRUE(dut.cell_known(id)) << id.c_str();
		EXPECT_FALSE(dut.cell_evaluable(id)) << id.c_str();
	}
}

TEST_F(CellTypesTest, AnyinitNotEvaluable)
{
	CellTypes dut;
	dut.setup();
	EXPECT_TRUE(dut.cell_known(ID($anyinit)));
	EXPECT_FALSE(dut.cell_evaluable(ID($anyinit)));
}

// TEST_F(CellTypesTest, OtherCellsNotEvaluable)
// {
// 	CellTypes dut;
// 	dut.setup();
// 	for (auto &id : {ID($assert), ID($assume), ID($cover), ID($print), ID($check), ID($connect), ID($scopeinfo)}) {
// 		EXPECT_TRUE(dut.cell_known(id)) << id.c_str();
// 		EXPECT_FALSE(dut.cell_evaluable(id)) << id.c_str();
// 	}
// }

TEST_F(CellTypesTest, AllEvalCellsAreEvaluable)
{
	CellTypes dut;
	dut.setup();
	for (auto &id : {ID($add), ID($sub), ID($mul), ID($and), ID($or), ID($xor), ID($not), ID($mux), ID($pmux), ID($shl), ID($shr), ID($lt), ID($le), ID($eq), ID($ne), ID($ge), ID($gt), ID($lcu), ID($alu), ID($fa), ID($bmux), ID($demux), ID($reduce_and), ID($reduce_or), ID($logic_not), ID($logic_and), ID($logic_or), ID($concat), ID($bweqx)}) {
		EXPECT_TRUE(dut.cell_evaluable(id)) << id.c_str();
	}
}

TEST_F(CellTypesTest, AllStdcellEvalCellsAreEvaluable)
{
	CellTypes dut;
	dut.setup();
	for (auto &id : {ID($_BUF_), ID($_NOT_), ID($_AND_), ID($_NAND_), ID($_OR_), ID($_NOR_), ID($_XOR_), ID($_XNOR_), ID($_ANDNOT_), ID($_ORNOT_), ID($_MUX_), ID($_NMUX_), ID($_MUX4_), ID($_MUX8_), ID($_MUX16_), ID($_AOI3_), ID($_OAI3_), ID($_AOI4_), ID($_OAI4_)}) {
		EXPECT_TRUE(dut.cell_evaluable(id)) << id.c_str();
	}
}

TEST_F(CellTypesTest, CellOutput_FalseForNonOutputPorts)
{
	CellTypes dut;
	dut.setup();
	EXPECT_TRUE(dut.cell_output(ID($add), ID::Y));
	EXPECT_FALSE(dut.cell_output(ID($add), ID::A));
	EXPECT_TRUE(dut.cell_output(ID($dff), ID::Q));
	EXPECT_FALSE(dut.cell_output(ID($dff), ID::Y));
}

TEST_F(CellTypesTest, CellInput_FalseForNonInputPorts)
{
	CellTypes dut;
	dut.setup();
	EXPECT_TRUE(dut.cell_input(ID($add), ID::A));
	EXPECT_FALSE(dut.cell_input(ID($add), ID::Y));
	EXPECT_TRUE(dut.cell_input(ID($dff), ID::D));
	EXPECT_FALSE(dut.cell_input(ID($dff), ID::Q));
}

TEST_F(CellTypesTest, AluPorts)
{
	CellTypes dut;
	dut.setup();
	EXPECT_TRUE(dut.cell_output(ID($alu), ID::X));
	EXPECT_TRUE(dut.cell_output(ID($alu), ID::Y));
	EXPECT_TRUE(dut.cell_output(ID($alu), ID::CO));
	EXPECT_TRUE(dut.cell_input(ID($alu), ID::A));
	EXPECT_TRUE(dut.cell_input(ID($alu), ID::BI));
	EXPECT_FALSE(dut.cell_input(ID($alu), ID::Y));
	EXPECT_TRUE(dut.cell_evaluable(ID($alu)));
}

TEST_F(CellTypesTest, FaPorts)
{
	CellTypes dut;
	dut.setup();
	EXPECT_TRUE(dut.cell_output(ID($fa), ID::X));
	EXPECT_TRUE(dut.cell_output(ID($fa), ID::Y));
	EXPECT_TRUE(dut.cell_input(ID($fa), ID::C));
	EXPECT_FALSE(dut.cell_output(ID($fa), ID::Q));
}

TEST_F(CellTypesTest, LcuPorts)
{
	CellTypes dut;
	dut.setup();
	EXPECT_TRUE(dut.cell_input(ID($lcu), ID::P));
	EXPECT_TRUE(dut.cell_input(ID($lcu), ID::G));
	EXPECT_TRUE(dut.cell_output(ID($lcu), ID::CO));
	EXPECT_FALSE(dut.cell_output(ID($lcu), ID::Y));
}

TEST_F(CellTypesTest, SetupSetsCorrectBits_Eval)
{
	CellTypes dut;
	dut.setup_internals_eval();
	EXPECT_TRUE(dut.enabled_cats & CellTypes::BIT_INTERNALS_EVAL);
	EXPECT_FALSE(dut.enabled_cats & CellTypes::BIT_INTERNALS_OTHER);
	EXPECT_FALSE(dut.enabled_cats & CellTypes::BIT_INTERNALS_FF);
}

TEST_F(CellTypesTest, SetupSetsCorrectBits_Internals)
{
	CellTypes dut;
	dut.setup_internals();
	EXPECT_TRUE(dut.enabled_cats & CellTypes::BIT_INTERNALS_EVAL);
	EXPECT_TRUE(dut.enabled_cats & CellTypes::BIT_INTERNALS_OTHER);
	EXPECT_FALSE(dut.enabled_cats & CellTypes::BIT_INTERNALS_FF);
	EXPECT_FALSE(dut.enabled_cats & CellTypes::BIT_INTERNALS_MEM);
}

TEST_F(CellTypesTest, SetupSetsCorrectBits_FF)
{
	CellTypes dut;
	dut.setup_internals_ff();
	EXPECT_TRUE(dut.enabled_cats & CellTypes::BIT_INTERNALS_FF);
	EXPECT_FALSE(dut.enabled_cats & CellTypes::BIT_INTERNALS_EVAL);
}

TEST_F(CellTypesTest, SetupSetsCorrectBits_Mem)
{
	CellTypes dut;
	dut.setup_internals_mem();
	EXPECT_TRUE(dut.enabled_cats & CellTypes::BIT_INTERNALS_FF);
	EXPECT_TRUE(dut.enabled_cats & CellTypes::BIT_INTERNALS_MEM);
}

TEST_F(CellTypesTest, SetupSetsCorrectBits_Anyinit)
{
	CellTypes dut;
	dut.setup_internals_anyinit();
	EXPECT_EQ(dut.enabled_cats, CellTypes::BIT_INTERNALS_ANYINIT);
}

TEST_F(CellTypesTest, SetupSetsCorrectBits_StdcellsEval)
{
	CellTypes dut;
	dut.setup_stdcells_eval();
	EXPECT_TRUE(dut.enabled_cats & CellTypes::BIT_STDCELLS_EVAL);
	EXPECT_FALSE(dut.enabled_cats & CellTypes::BIT_STDCELLS_TRISTATE);
}

TEST_F(CellTypesTest, SetupSetsCorrectBits_Stdcells)
{
	CellTypes dut;
	dut.setup_stdcells();
	EXPECT_TRUE(dut.enabled_cats & CellTypes::BIT_STDCELLS_EVAL);
	EXPECT_TRUE(dut.enabled_cats & CellTypes::BIT_STDCELLS_TRISTATE);
	EXPECT_FALSE(dut.enabled_cats & CellTypes::BIT_STDCELLS_FF);
}

TEST_F(CellTypesTest, SetupSetsCorrectBits_StdcellsMem)
{
	CellTypes dut;
	dut.setup_stdcells_mem();
	EXPECT_TRUE(dut.enabled_cats & CellTypes::BIT_STDCELLS_FF);
	EXPECT_FALSE(dut.enabled_cats & CellTypes::BIT_STDCELLS_EVAL);
}

TEST_F(CellTypesTest, SetupSetsCorrectBits_Full)
{
	CellTypes dut;
	dut.setup();
	EXPECT_EQ(dut.enabled_cats, CellTypes::BITS_ALL);
}

YOSYS_NAMESPACE_END
