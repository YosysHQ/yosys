#include <gtest/gtest.h>

#include "kernel/rtlil.h"
#include "kernel/sigtools.h"
#include "passes/opt/clean/opt_clean.h"
#include "kernel/yosys.h"

namespace {
	struct YosysSetupEnvironment : ::testing::Environment {
		void SetUp() override { Yosys::yosys_setup(); }
	};
	const ::testing::Environment *yosys_setup_env =
		::testing::AddGlobalTestEnvironment(new YosysSetupEnvironment);
}

YOSYS_NAMESPACE_BEGIN

class OptCleanSignormTest : public ::testing::Test {
protected:
	RTLIL::Design *design;
	RTLIL::Module *module;

	void SetUp() override {
		design = new RTLIL::Design;
		module = design->addModule(id("\\top"));
	}

	void TearDown() override {
		if (design->flagSigNormalized)
			design->sigNormalize(false);
		delete design;
	}

	RTLIL::IdString id(const std::string &name) { return RTLIL::IdString(name); }

	RTLIL::Wire *wire(const std::string &name, int width = 1) {
		return module->addWire(id(name), width);
	}

	RTLIL::Wire *input(const std::string &name, int width = 1) {
		RTLIL::Wire *w = wire(name, width);
		w->port_input = true;
		return w;
	}

	RTLIL::Wire *output(const std::string &name, int width = 1) {
		RTLIL::Wire *w = wire(name, width);
		w->port_output = true;
		return w;
	}

	void normalize() {
		module->fixup_ports();
		design->sigNormalize(true);
	}

	RmStats sweep(bool purge = false) {
		std::vector<RTLIL::Module *> modules{module};
		CleanRunContext clean_ctx(design, modules, Flags{purge, false});
		int workers = ThreadPool::work_pool_size(0, opt_clean_work_units(module), 10000);
		ParallelDispatchThreadPool::Subpool subpool(clean_ctx.thread_pool, workers);
		rmunused_module_signorm(module, subpool, clean_ctx);
		return clean_ctx.stats;
	}

	bool hasCell(const std::string &name) { return module->cell(id(name)) != nullptr; }
	bool hasWire(const std::string &name) { return module->wire(id(name)) != nullptr; }

	int countCells(RTLIL::IdString type = RTLIL::IdString()) {
		int count = 0;
		for (RTLIL::Cell *cell : module->cells()) {
			if (!type.empty()) {
				if (cell->type == type)
					count++;
				continue;
			}
			if (!cell->type.in(ID($input_port), ID($connect)))
				count++;
		}
		return count;
	}
	void expectIndexConsistent() {
		ASSERT_TRUE(module->signorm_indexed());

		for (auto &[bit, portbits] : module->signorm_fanout()) {
			for (auto &pb : portbits) {
				ASSERT_TRUE(pb.cell->hasPort(pb.port));
				const RTLIL::SigSpec &sig = pb.cell->getPort(pb.port);
				ASSERT_GE(pb.offset, 0);
				ASSERT_LT(pb.offset, sig.size());
				EXPECT_EQ(sig[pb.offset], bit);
			}
		}

		for (RTLIL::Cell *cell : module->cells()) {
			for (auto &[port, sig] : cell->connections()) {
				if (cell->port_dir(port) != RTLIL::PD_INPUT)
					continue;
				int i = 0;
				for (auto bit : sig) {
					if (bit.is_wire())
						EXPECT_TRUE(module->fanout(bit).count(RTLIL::PortBit(cell, port, i)));
					i++;
				}
			}
		}

		for (RTLIL::Wire *wire : module->wires()) {
			if (!wire->known_driver()) {
				EXPECT_FALSE(wire->port_input && !wire->port_output);
				continue;
			}
			RTLIL::Cell *driver = wire->driverCell();
			ASSERT_TRUE(driver->hasPort(wire->driverPort()));
			const RTLIL::SigSpec &dsig = driver->getPort(wire->driverPort());
			ASSERT_TRUE(dsig.is_wire());
			EXPECT_EQ(dsig.as_wire(), wire);
		}
	}
};

TEST_F(OptCleanSignormTest, CountsWhatItRemoves) {
	RTLIL::Wire *a = input("\\a");
	RTLIL::Wire *y = output("\\y");
	RTLIL::Wire *live = wire("$live");
	RTLIL::Wire *dead = wire("$dead");

	RTLIL::Cell *keeper = module->addCell(id("$keeper"), ID($_NOT_));
	keeper->setPort(ID::A, a);
	keeper->setPort(ID::Y, live);

	RTLIL::Cell *waste = module->addCell(id("$waste"), ID($_NOT_));
	waste->setPort(ID::A, a);
	waste->setPort(ID::Y, dead);

	module->connect(y, live);
	normalize();

	RmStats stats = sweep();

	EXPECT_EQ(stats.count_rm_cells, 1);
	EXPECT_EQ(stats.count_rm_wires, 1);
	EXPECT_TRUE(hasCell("$keeper"));
	EXPECT_FALSE(hasCell("$waste"));
	EXPECT_FALSE(hasWire("$dead"));
	expectIndexConsistent();
}

TEST_F(OptCleanSignormTest, SecondSweepIsANoOp) {
	RTLIL::Wire *a = input("\\a");
	RTLIL::Wire *y = output("\\y");
	RTLIL::Wire *dead = wire("$dead");

	RTLIL::Cell *keeper = module->addCell(id("$keeper"), ID($_NOT_));
	keeper->setPort(ID::A, a);
	keeper->setPort(ID::Y, y);

	RTLIL::Cell *waste = module->addCell(id("$waste"), ID($_NOT_));
	waste->setPort(ID::A, a);
	waste->setPort(ID::Y, dead);

	normalize();

	RmStats first = sweep();
	ASSERT_GT(first.count_rm_cells, 0);

	int cells = countCells(), wires = module->wires_size();
	RmStats second = sweep();

	EXPECT_EQ(second.count_rm_cells, 0);
	EXPECT_EQ(second.count_rm_wires, 0);
	EXPECT_EQ(countCells(), cells);
	EXPECT_EQ(module->wires_size(), wires);
	expectIndexConsistent();
}

TEST_F(OptCleanSignormTest, InputPortMarkersSurvive) {
	RTLIL::Wire *a = input("\\a");
	RTLIL::Wire *y = output("\\y");

	RTLIL::Cell *inv = module->addCell(id("$inv"), ID($_NOT_));
	inv->setPort(ID::A, a);
	inv->setPort(ID::Y, y);

	normalize();

	ASSERT_EQ(countCells(ID($input_port)), 1);
	ASSERT_TRUE(a->known_driver());
	EXPECT_EQ(a->driverCell()->type, ID($input_port));

	sweep();

	EXPECT_EQ(countCells(ID($input_port)), 1);
	EXPECT_TRUE(a->known_driver());
	expectIndexConsistent();
}

TEST_F(OptCleanSignormTest, LivenessCrossesConnectCells) {
	RTLIL::Wire *a = input("\\a");
	RTLIL::Wire *y = output("\\y");
	RTLIL::Wire *left = wire("$left");
	RTLIL::Wire *right = wire("$right");

	RTLIL::Cell *lhs = module->addCell(id("$lhs"), ID($_NOT_));
	lhs->setPort(ID::A, a);
	lhs->setPort(ID::Y, left);

	RTLIL::Cell *rhs = module->addCell(id("$rhs"), ID($_NOT_));
	rhs->setPort(ID::A, a);
	rhs->setPort(ID::Y, right);

	module->connect(left, right);
	module->connect(y, left);
	normalize();
	ASSERT_EQ(countCells(ID($connect)), 1);

	sweep();

	EXPECT_TRUE(hasCell("$lhs"));
	EXPECT_TRUE(hasCell("$rhs"));
	EXPECT_EQ(countCells(ID($connect)), 1);
	expectIndexConsistent();
}

TEST_F(OptCleanSignormTest, DeadConnectCellIsCollected) {
	RTLIL::Wire *a = input("\\a");
	RTLIL::Wire *left = wire("$left");
	RTLIL::Wire *right = wire("$right");

	RTLIL::Cell *lhs = module->addCell(id("$lhs"), ID($_NOT_));
	lhs->setPort(ID::A, a);
	lhs->setPort(ID::Y, left);

	RTLIL::Cell *rhs = module->addCell(id("$rhs"), ID($_NOT_));
	rhs->setPort(ID::A, a);
	rhs->setPort(ID::Y, right);

	module->connect(left, right);
	normalize();
	ASSERT_EQ(countCells(ID($connect)), 1);

	RmStats stats = sweep();

	EXPECT_EQ(stats.count_rm_cells, 3);
	EXPECT_EQ(countCells(ID($connect)), 0);
	EXPECT_FALSE(hasCell("$lhs"));
	EXPECT_FALSE(hasCell("$rhs"));
	expectIndexConsistent();
}

TEST_F(OptCleanSignormTest, PurgeDropsPublicAliases) {
	RTLIL::Wire *a = input("\\a");
	RTLIL::Wire *y = output("\\y");
	RTLIL::Wire *alias = wire("\\alias");

	RTLIL::Cell *inv = module->addCell(id("$inv"), ID($_NOT_));
	inv->setPort(ID::A, a);
	inv->setPort(ID::Y, y);

	module->connect(alias, y);
	normalize();

	sweep();
	EXPECT_TRUE(hasWire("\\alias"));

	sweep(true);
	EXPECT_FALSE(hasWire("\\alias"));
	EXPECT_TRUE(hasWire("\\y"));
	expectIndexConsistent();
}

TEST_F(OptCleanSignormTest, InitMovesToRepresentativeAndPinsIt) {
	RTLIL::Wire *a = input("\\a");
	RTLIL::Wire *y = output("\\y");
	RTLIL::Wire *driven = wire("$driven");
	RTLIL::Wire *alias = wire("$alias");

	RTLIL::Cell *inv = module->addCell(id("$inv"), ID($_NOT_));
	inv->setPort(ID::A, a);
	inv->setPort(ID::Y, driven);

	alias->attributes[ID::init] = RTLIL::Const(State::S1, 1);

	module->connect(alias, driven);
	module->connect(y, driven);
	normalize();

	sweep();

	EXPECT_FALSE(hasWire("$alias"));
	ASSERT_TRUE(hasWire("$driven"));
	RTLIL::Wire *rep = module->wire(id("$driven"));
	ASSERT_EQ(rep->attributes.count(ID::init), 1);
	EXPECT_EQ(rep->attributes.at(ID::init), RTLIL::Const(State::S1, 1));
	expectIndexConsistent();
}

TEST_F(OptCleanSignormTest, InitPinsWireButAllXDoesNot) {
	RTLIL::Wire *pinned = wire("$pinned");
	RTLIL::Wire *undef = wire("$undef");

	pinned->attributes[ID::init] = RTLIL::Const(State::S0, 1);
	undef->attributes[ID::init] = RTLIL::Const(State::Sx, 1);

	normalize();
	sweep();

	EXPECT_TRUE(hasWire("$pinned"));
	EXPECT_FALSE(hasWire("$undef"));
	EXPECT_EQ(module->wire(id("$pinned"))->attributes.count(ID::init), 1);
	expectIndexConsistent();
}

TEST_F(OptCleanSignormTest, BuffersCollapseUnlessKept) {
	RTLIL::Wire *a = input("\\a");
	RTLIL::Wire *y1 = output("\\y1");
	RTLIL::Wire *y2 = output("\\y2");
	RTLIL::Wire *mid = wire("$mid");

	RTLIL::Cell *buf = module->addCell(id("$buf_cell"), ID($_BUF_));
	buf->setPort(ID::A, a);
	buf->setPort(ID::Y, mid);

	RTLIL::Cell *pos = module->addCell(id("$pos_cell"), ID($pos));
	pos->setParam(ID::A_SIGNED, 0);
	pos->setParam(ID::A_WIDTH, 1);
	pos->setParam(ID::Y_WIDTH, 1);
	pos->setPort(ID::A, mid);
	pos->setPort(ID::Y, y1);

	RTLIL::Cell *kept = module->addCell(id("$kept_cell"), ID($_BUF_));
	kept->setPort(ID::A, a);
	kept->setPort(ID::Y, y2);
	kept->set_bool_attribute(ID::keep);

	normalize();
	sweep();

	EXPECT_FALSE(hasCell("$buf_cell"));
	EXPECT_FALSE(hasCell("$pos_cell"));
	EXPECT_TRUE(hasCell("$kept_cell"));
	expectIndexConsistent();
}

TEST_F(OptCleanSignormTest, LongChainAtThreadPoolScale) {
	const int length = 25000;

	RTLIL::Wire *a = input("\\a");
	RTLIL::Wire *y = output("\\y");

	RTLIL::SigSpec prev = a;
	for (int i = 0; i < length; i++) {
		RTLIL::Wire *next = wire(stringf("$chain%d", i));
		RTLIL::Cell *stage = module->addCell(id(stringf("$stage%d", i)), ID($_NOT_));
		stage->setPort(ID::A, prev);
		stage->setPort(ID::Y, next);
		prev = next;
	}

	RTLIL::Wire *dead = wire("$dead");
	RTLIL::Cell *waste = module->addCell(id("$waste"), ID($_NOT_));
	waste->setPort(ID::A, a);
	waste->setPort(ID::Y, dead);

	module->connect(y, prev);
	normalize();

	RmStats stats = sweep();

	EXPECT_EQ(stats.count_rm_cells, 1);
	EXPECT_EQ(countCells(), length);
	EXPECT_FALSE(hasCell("$waste"));
	EXPECT_TRUE(hasCell("$stage0"));
	EXPECT_TRUE(hasCell(stringf("$stage%d", length - 1)));
	expectIndexConsistent();
}

YOSYS_NAMESPACE_END
