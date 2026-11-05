#include <gtest/gtest.h>

#include <fstream>
#include <thread>
#include <vector>

#include "kernel/register.h"

YOSYS_NAMESPACE_BEGIN

const char *design_source = R"(
module top
(
    input [3:0] x,
    input [3:0] y,

    output [3:0] A,
    output [3:0] B
);

    assign A =  x + y;
    assign B =  x - y;
endmodule
)";

TEST(VerificThreadingTest, DesignsConcurrencyCheck)
{
	if (logger().empty())
		logger().add_sink<StderrLogSink>(false);

	const std::string filename = make_temp_file(get_base_tmpdir() + "/yosys_verific_XXXXXX.sv");
	std::ofstream(filename) << design_source;

	std::vector<std::thread> threads;
	for (int i = 0; i < 8; ++i) {
		threads.emplace_back([&] {
			RTLIL::Design design;
			Pass::call(&design, "verific -sv " + filename);
			Pass::call(&design, "hierarchy -top top");
			EXPECT_NE(design.module(ID(top)), nullptr);
		});
	}
	for (auto &thread : threads)
		thread.join();

	remove(filename.c_str());
}

YOSYS_NAMESPACE_END
