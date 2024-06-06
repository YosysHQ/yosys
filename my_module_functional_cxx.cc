#include "sim.h"
struct gold_Inputs {
	Signal<4> B;
	Signal<5> A;

	template <typename T> void dump(T &out) const {
		out("B", B);
		out("A", A);
	}

	int size() const {
		return 2;
	}

	std::variant<std::reference_wrapper<Signal<4>>, std::reference_wrapper<Signal<5>>> get_input(const int index) const {
		switch (index) {
			case 0: return std::ref(B);
			case 1: return std::ref(A);
			default: throw std::out_of_range("Invalid input index");
		}
	}
};

struct gold_Outputs {
	Signal<6> Y;

	template <typename T> void dump(T &out) const {
		out("Y", Y);
	}

};

struct gold_State {

	template <typename T> void dump(T &out) const {
	}

};

void gold(gold_Inputs const &input, gold_Outputs &output, gold_State const &current_state, gold_State &next_state)
{
	Signal<4> B = input.B;
	Signal<5> A = input.A;
	Signal<6> n2 = $sign_extend<6>(A); //[WIDTH=6]
	Signal<6> n3 = $sign_extend<6>(B); //[WIDTH=6]
	Signal<6> UUT$_Y = $add(n2, n3); //
	output.Y = UUT$_Y;
}
