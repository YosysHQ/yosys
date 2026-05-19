#include <gtest/gtest.h>

#include "kernel/rtlil.h"
#include "tests/unit/kernel/rtlilHelpers.h"

YOSYS_NAMESPACE_BEGIN

namespace RTLIL {
	TEST_F(SigSpecRepTest, Extract)
	{
		{
			std::vector<Wire*> wires;
			SigSpec sig;
			for (int i = 0; i < 4; i++)
				wires.push_back(m->addWire(stringf("$w%d", i), 4));
			for (auto w : wires)
				sig.append(w);

			SigSpec extractedFirst = sig.extract(0, 4);
			SigSpec extractedSecond = sig.extract(4, 4);
			SigSpec extractedLast = sig.extract(12, 4);
			EXPECT_EQ(extractedFirst.rep_, SigSpec::Representation::CHUNK);
			EXPECT_EQ(extractedSecond.rep_, SigSpec::Representation::CHUNK);
			EXPECT_EQ(extractedLast.rep_, SigSpec::Representation::CHUNK);
			EXPECT_EQ(extractedFirst.as_wire(), wires[0]);
			EXPECT_EQ(extractedSecond.as_wire(), wires[1]);
			EXPECT_EQ(extractedLast.as_wire(), wires[3]);
		}

		{
			std::vector<SigSpec> consts;
			SigSpec sig;
			for (int i = 0; i < 4; i++)
				consts.push_back(Const(i, 4));
			for (auto c : consts)
				sig.append(c);

			SigSpec extractedFirst = sig.extract(0, 4);
			SigSpec extractedSecond = sig.extract(4, 4);
			SigSpec extractedLast = sig.extract(12, 4);
			EXPECT_EQ(extractedFirst.rep_, SigSpec::Representation::CHUNK);
			EXPECT_EQ(extractedSecond.rep_, SigSpec::Representation::CHUNK);
			EXPECT_EQ(extractedLast.rep_, SigSpec::Representation::CHUNK);
			EXPECT_EQ(extractedFirst, consts[0]);
			EXPECT_EQ(extractedSecond, consts[1]);
			EXPECT_EQ(extractedLast, consts[3]);
		}

		{
			SigSpec sig;
			sig.append(Const(0, 4));
			Wire* w = m->addWire("$foo", 4);
			sig.append(w);
			sig.append(Const(15, 4));

			SigSpec extractedFirst = sig.extract(0, 4);
			SigSpec extractedSecond = sig.extract(4, 4);
			SigSpec extractedLast = sig.extract(8, 4);
			EXPECT_EQ(extractedFirst.rep_, SigSpec::Representation::CHUNK);
			EXPECT_EQ(extractedSecond.rep_, SigSpec::Representation::CHUNK);
			EXPECT_EQ(extractedLast.rep_, SigSpec::Representation::CHUNK);

			SigSpec extractedFirstTwo = sig.extract(0, 8);
			EXPECT_EQ(extractedFirstTwo.rep_, SigSpec::Representation::BITS);
			SigSpec extractedLastTwo = sig.extract(4, 8);
			EXPECT_EQ(extractedLastTwo.rep_, SigSpec::Representation::BITS);

			EXPECT_EQ(extractedFirstTwo[0], State::S0);
			EXPECT_EQ(extractedFirstTwo[1], State::S0);
			EXPECT_EQ(extractedFirstTwo[2], State::S0);
			EXPECT_EQ(extractedFirstTwo[3], State::S0);
			EXPECT_EQ(extractedFirstTwo[4], SigBit(w, 0));
			EXPECT_EQ(extractedFirstTwo[5], SigBit(w, 1));
			EXPECT_EQ(extractedFirstTwo[6], SigBit(w, 2));
			EXPECT_EQ(extractedFirstTwo[7], SigBit(w, 3));

			EXPECT_EQ(extractedLastTwo[0], SigBit(w, 0));
			EXPECT_EQ(extractedLastTwo[1], SigBit(w, 1));
			EXPECT_EQ(extractedLastTwo[2], SigBit(w, 2));
			EXPECT_EQ(extractedLastTwo[3], SigBit(w, 3));
			EXPECT_EQ(extractedLastTwo[4], State::S1);
			EXPECT_EQ(extractedLastTwo[5], State::S1);
			EXPECT_EQ(extractedLastTwo[6], State::S1);
			EXPECT_EQ(extractedLastTwo[7], State::S1);
		}
	}
};

YOSYS_NAMESPACE_END
