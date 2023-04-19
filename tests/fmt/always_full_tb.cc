#include "yosys-always_full.cc"

int main()
{
	cxxrtl_design::p_always__full uut;
	uut.p_clk.set(!uut.p_clk);
	uut.step();
	return 0;
}
