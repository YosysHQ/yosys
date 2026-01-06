#include "yosys-always_comb.cc"

int main()
{
	cxxrtl_design::p_top uut1, uut2;

	for (int i = 0; i < 20; ++i) {
		uut1.p_clk.set(!uut1.p_clk);
		uut1.step();

		uut2.p_clk.set(!uut2.p_clk);
		uut2.step();
	}

	return 0;
}
