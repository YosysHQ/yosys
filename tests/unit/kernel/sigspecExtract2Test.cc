#include <gtest/gtest.h>

#include "kernel/rtlil.h"
#include "tests/unit/kernel/rtlilHelpers.h"

YOSYS_NAMESPACE_BEGIN

namespace RTLIL {
	TEST_F(SigSpecRepTest, ExtractWires)
	{
		auto wires = createWires(4, 4);
		SigSpec sig = wiresAsSigSpec(wires);

		SigSpec extractedFirst = sig.extract(0, 4);
		SigSpec extractedSecond = sig.extract(4, 4);
		SigSpec extractedLast = sig.extract(12, 4);
		EXPECT_EQ(extractedFirst.rep_, SigSpec::Representation::CHUNK);
		EXPECT_EQ(extractedSecond.rep_, SigSpec::Representation::CHUNK);
		EXPECT_EQ(extractedLast.rep_, SigSpec::Representation::CHUNK);
	}

	TEST_F(SigSpecRepTest, ExtractConsts)
	{
		{
			SigSpec sig = constsAsSigSpec(4, 4);

			SigSpec extractedFirst = sig.extract(0, 4);
			SigSpec extractedSecond = sig.extract(4, 4);
			SigSpec extractedLast = sig.extract(12, 4);
			std::cout << log_signal(extractedFirst) << "\n";
			EXPECT_EQ(extractedFirst.rep_, SigSpec::Representation::CHUNK);
			EXPECT_EQ(extractedSecond.rep_, SigSpec::Representation::CHUNK);
			EXPECT_EQ(extractedLast.rep_, SigSpec::Representation::CHUNK);
		}

		{
			SigSpec sig;
			sig.append(Const(0, 4));
			sig.append(m->addWire("$foo", 4));
			sig.append(Const(0, 4));

			SigSpec extractedFirst = sig.extract(0, 4);
			SigSpec extractedSecond = sig.extract(4, 4);
			SigSpec extractedLast = sig.extract(8, 4);
			EXPECT_EQ(extractedFirst.rep_, SigSpec::Representation::CHUNK);
			EXPECT_EQ(extractedSecond.rep_, SigSpec::Representation::CHUNK);
			EXPECT_EQ(extractedLast.rep_, SigSpec::Representation::CHUNK);

			SigSpec extractedFirstTwo = sig.extract(0, 8);
			EXPECT_EQ(extractedFirstTwo.rep_, SigSpec::Representation::BITS);
			SigSpec extractedLastTwo = sig.extract(0, 8);
			EXPECT_EQ(extractedLastTwo.rep_, SigSpec::Representation::BITS);
		}
	}
};

YOSYS_NAMESPACE_END
