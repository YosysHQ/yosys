#include <gtest/gtest.h>

#include <fstream>
#include <sstream>
#include <thread>
#include <vector>

#include "kernel/register.h"
#include "kernel/rtlil.h"
#include "backends/rtlil/rtlil_backend.h"

YOSYS_NAMESPACE_BEGIN

static const char *threaded_source = R"(
interface bus #(parameter W = 4);
	logic [W-1:0] d;
endinterface

(* frontend_test_mod *)
module sub #(parameter W = 4) (bus b, input [W-1:0] x);
	typedef enum logic [1:0] { IDLE, RUN } state_t;
	(* frontend_test_wire *) state_t s;
	assign s = x[0] ? RUN : IDLE;
	assign b.d = x + s;
endmodule

module top #(parameter W = 4) (input [W-1:0] x, output [W-1:0] y);
	bus #(.W(W)) b();
	sub #(.W(W)) u(.b(b), .x(x));
	assign y = b.d;
endmodule
)";

static const char *attr_source = R"(
(* frontend_test_mod *)
module sub #(parameter W = 1) (input [W-1:0] a, output [W-1:0] y);
	(* frontend_test_wire *) wire [W-1:0] t = ~a;
	assign y = t;
endmodule
)";

class VerilogFrontendTest : public testing::Test {
protected:
	std::string dir;

	VerilogFrontendTest() {
		dir = make_temp_dir(get_base_tmpdir() + "/yosys_verilog_XXXXXX");
		std::ofstream(dir + "/threaded.sv") << threaded_source;
		std::ofstream(dir + "/attr.v") << attr_source;
		std::ofstream(dir + "/a1.v") << "module a1; endmodule\n";
		std::ofstream(dir + "/a2.v") << "module a2; endmodule\n";
	}

	~VerilogFrontendTest() {
		remove_directory(dir);
	}

	std::unique_ptr<RTLIL::Design> elaborate() {
		auto design = std::make_unique<RTLIL::Design>();
		Pass::call(design.get(), "read_verilog -sv -defer " + dir + "/threaded.sv");
		Pass::call(design.get(), "hierarchy -top top");
		RTLIL::SigSpec sig;
		EXPECT_TRUE(RTLIL::SigSpec::parse(sig, nullptr, "8'hx5,4'sd3"));
		EXPECT_EQ(GetSize(sig), 12);
		return design;
	}

	static std::string dump(RTLIL::Design *design) {
		std::ostringstream rtlil;
		RTLIL_BACKEND::dump_design(rtlil, design, false);
		return rtlil.str();
	}

	void expect_attrs(RTLIL::Design &design) {
		Pass::call(&design, "hierarchy -top sub -chparam W 3");
		RTLIL::Module *top = design.top_module();
		ASSERT_NE(top, nullptr);
		EXPECT_TRUE(top->attributes.count(design.twines().find("\\frontend_test_mod")));
		RTLIL::Wire *t = top->wire(design.twines().find("\\t"));
		ASSERT_NE(t, nullptr);
		EXPECT_TRUE(t->attributes.count(design.twines().find("\\frontend_test_wire")));
	}
};

TEST_F(VerilogFrontendTest, ConcurrentDesignsMatchSerial)
{
	std::string reference = dump(elaborate().get());
	std::vector<std::unique_ptr<RTLIL::Design>> designs(32);
	std::vector<std::thread> threads;
	for (int i = 0; i < 8; ++i)
		threads.emplace_back([&, i] {
			for (int iter = 0; iter < 4; ++iter)
				designs[i * 4 + iter] = elaborate();
		});
	for (auto &thread : threads)
		thread.join();
	for (auto &design : designs)
		EXPECT_EQ(dump(design.get()), reference);
}

TEST_F(VerilogFrontendTest, NextArgsResetAfterError)
{
	RTLIL::Design design;
	auto guard = logger().error_throw_scope();
	EXPECT_THROW(Pass::call(&design, "read_verilog " + dir + "/a*.v -foo"), log_cmd_error_exception);
	Pass::call(&design, "read_verilog " + dir + "/a1.v");
	EXPECT_EQ(GetSize(design.modules()), 1);
}

TEST_F(VerilogFrontendTest, DeferredAttrsSurviveGc)
{
	RTLIL::Design design;
	Pass::call(&design, "read_verilog -defer " + dir + "/attr.v");
	design.gc_twines();
	expect_attrs(design);
}

TEST_F(VerilogFrontendTest, DeferredAttrsSurviveCopy)
{
	RTLIL::Design src, dst;
	Pass::call(&src, "read_verilog -defer " + dir + "/attr.v");
	src.module(src.twines().find("$abstract\\sub"))->clone(&dst);
	expect_attrs(dst);
}

YOSYS_NAMESPACE_END
