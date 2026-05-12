// Note: Use `cmake -DYOSYS_INSTALL_LIBRARY=1` or build the `libyosys` target first
// yosys-config --exec --cxx -o demomain --cxxflags --ldflags demomain.cc -lyosys

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

