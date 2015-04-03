// clang -o example -std=c++11 -I/usr/include/tcl8.5 -I include/ example.cc objs/*.o -lstdc++ -lm -lrt -lreadline -lffi -ldl -ltcl8.5

#include <yosys.h>

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

