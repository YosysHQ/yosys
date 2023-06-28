#include <iostream>
#include "yosys-always_full.cc"

int main()
{
	cxxrtl_design::p_always__full uut;

	while (true) {
		uut.p_clk.set(!uut.p_clk);
		uut.step();

		if (uut.p_fin.get<bool>())
			return 0;
	}
}
