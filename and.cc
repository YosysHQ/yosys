#include "sim.h"
struct my_module_Inputs {
	Signal<1> b;
	Signal<1> a;

	template <typename T> void dump(T &out) {
		out("b", b);
		out("a", a);
	}
};

struct my_module_Outputs {
	Signal<1> sum;

	template <typename T> void dump(T &out) {
		out("sum", sum);
	}
};

struct my_module_State {

	template <typename T> void dump(T &out) {
	}
};

void my_module(my_module_Inputs const &input, my_module_Outputs &output, my_module_State const &current_state, my_module_State &next_state)
{
	Signal<1> b = input.b;
	Signal<1> a = input.a;
	Signal<1> $add$tests_functional_single_bit_verilog_my_module_add_v_7$1$_Y = $add(a, b); //
	output.sum = $add$tests_functional_single_bit_verilog_my_module_add_v_7$1$_Y;
}
