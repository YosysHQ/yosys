// Note: Set ENABLE_LIBYOSYS=1 in Makefile or Makefile.conf to build libyosys.so
// yosys-config --exec --cxx -o demomain --cxxflags --ldflags demomain.cc -lyosys -lstdc++

#include <kernel/yosys.h>

int main()
{
	Yosys::log_streams.push_back(&std::cout);
	Yosys::log_error_stderr = true;

	Yosys::yosys_setup();
	Yosys::yosys_banner();

	Yosys::run_pass("read_verilog example.v");
	Yosys::run_pass("synth -noabc");
	Yosys::run_pass("clean -purge");
	Yosys::run_pass("write_blif example.blif");

	Yosys::yosys_shutdown();
	return 0;
}

