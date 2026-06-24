#ifndef YOSYS_SETUP_ENV_H
#define YOSYS_SETUP_ENV_H

#include <gtest/gtest.h>

#include "kernel/yosys.h"

namespace {
	struct YosysSetupEnvironment : ::testing::Environment {
		void SetUp() override { Yosys::yosys_setup(); }
	};
	const ::testing::Environment *yosys_setup_env =
		::testing::AddGlobalTestEnvironment(new YosysSetupEnvironment);
}

#endif /* YOSYS_SETUP_ENV_H */
