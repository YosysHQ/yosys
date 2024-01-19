#include "yosys-always_full.cc"

int main()
{
	struct : public performer {
		int64_t vlog_time() const override { return 1; }
		void on_print(const lazy_fmt &output, const cxxrtl::metadata_map &) override { std::cerr << output(); }
	} performer;

	cxxrtl_design::p_always__full uut;
	uut.p_clk.set(!uut.p_clk);
	uut.step(&performer);
	return 0;
}
