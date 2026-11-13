#include <gtest/gtest.h>

#include <fstream>
#include <thread>
#include <vector>

#include "kernel/register.h"
#include "kernel/rtlil.h"
#include "frontends/verilog/verilog_frontend.h"

YOSYS_NAMESPACE_BEGIN

static const char *design_source = R"(
`define SUB_WIDTH 4
module sub #(parameter W = 1) (input [W-1:0] a, b, output [W-1:0] y);
	assign y = a + b + 'hx;
endmodule

module top #(parameter N = 2) (input [N*`SUB_WIDTH-1:0] x, y, output [N*`SUB_WIDTH-1:0] s);
	genvar i;
	generate for (i = 0; i < N; i = i + 1) begin : g
		sub #(.W(`SUB_WIDTH)) u (.a(x[i*`SUB_WIDTH +: `SUB_WIDTH]), .b(y[i*`SUB_WIDTH +: `SUB_WIDTH]), .y(s[i*`SUB_WIDTH +: `SUB_WIDTH]));
	end endgenerate
endmodule
)";

class VerilogThreadingTest : public testing::Test {
protected:
	std::string filename;

	VerilogThreadingTest() {
		filename = make_temp_file(get_base_tmpdir() + "/yosys_verilog_XXXXXX.v");
		std::ofstream(filename) << design_source;
	}

	~VerilogThreadingTest() {
		remove(filename.c_str());
	}
};

TEST_F(VerilogThreadingTest, ReadAndElaborate)
{
	VERILOG_FRONTEND::VerilogDefaultsFreeze freeze;
	std::vector<std::thread> threads;
	for (int i = 0; i < 8; ++i) {
		threads.emplace_back([&, i] {
			for (int iter = 0; iter < 4; ++iter) {
				RTLIL::Design design;
				Pass::call(&design, i % 2 ? "read_verilog -defer " + filename : "read_verilog " + filename);
				Pass::call(&design, "hierarchy -top top -chparam N " + std::to_string(i + 1));
				EXPECT_NE(design.top_module(), nullptr);
				EXPECT_EQ(GetSize(design.modules()), 2);
			}
		});
	}
	for (auto &thread : threads)
		thread.join();
}

TEST_F(VerilogThreadingTest, ConstParseDuringRead)
{
	VERILOG_FRONTEND::VerilogDefaultsFreeze freeze;
	std::atomic<bool> done = false;
	std::vector<std::thread> parsers;
	for (int i = 0; i < 4; ++i) {
		parsers.emplace_back([&] {
			while (!done.load()) {
				RTLIL::SigSpec sig;
				EXPECT_TRUE(RTLIL::SigSpec::parse(sig, nullptr, "8'hx5,4'sd3,1'b1"));
				EXPECT_EQ(GetSize(sig), 13);
			}
		});
	}
	std::vector<std::thread> readers;
	for (int i = 0; i < 4; ++i) {
		readers.emplace_back([&] {
			for (int iter = 0; iter < 4; ++iter) {
				RTLIL::Design design;
				Pass::call(&design, "read_verilog " + filename);
				Pass::call(&design, "hierarchy -top top");
				EXPECT_NE(design.top_module(), nullptr);
			}
		});
	}
	for (auto &thread : readers)
		thread.join();
	done = true;
	for (auto &thread : parsers)
		thread.join();
}

TEST_F(VerilogThreadingTest, DefaultsFrozen)
{
	RTLIL::Design design;
	logger().set_cmd_error_throw(true);
	{
		VERILOG_FRONTEND::VerilogDefaultsFreeze freeze;
		EXPECT_THROW(Pass::call(&design, "verilog_defaults -add -sv"), log_cmd_error_exception);
	}
	Pass::call(&design, "verilog_defaults -push");
	Pass::call(&design, "verilog_defaults -pop");
	logger().set_cmd_error_throw(false);
}

YOSYS_NAMESPACE_END
