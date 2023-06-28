#include <iostream>
#include "yosys-always_comb.cc"

int main()
{
	cxxrtl_design::p_top uut;

	for (int i = 0; i < 20; ++i) {
		uut.p_clk.set(!uut.p_clk);
		uut.step();
	}

	return 0;
}
