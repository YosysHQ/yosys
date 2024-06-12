#include <cstdio>
#include <iostream>
#include <fstream>
#include <random>

#include "my_module_functional_cxx.cc"

struct DumpHeader {
  std::ofstream &ofs;
  DumpHeader(std::ofstream &ofs) : ofs(ofs) {}
  template <size_t n>
  void operator()(const char *name, Signal<n> value) {
    ofs << "$var wire " << n << " " << name[0] << " " << name << " $end\n";
  }
};

struct Dump {
  std::ofstream &ofs;
  Dump(std::ofstream &ofs) : ofs(ofs) {}
  template <size_t n>
  void operator()(const char *name, Signal<n> value) {
    // Bit
    if (n == 1) {
      ofs << (value[0] ? '1' : '0');
      ofs << name[0] << "\n";
      return;
    }
    // vector (multi-bit) signals
    ofs << "b";
    for (size_t i = n; i-- > 0;)
      ofs << (value[i] ? '1' : '0');
    ofs << " " << name[0] << "\n";
  }
};

// Function to set all values in a signal to false
template<std::size_t n>
void set_all_false(Signal<n>& signal) {
  std::fill(signal.begin(), signal.end(), false);
}

template<std::size_t n>
void set_all_random(Signal<n>& signal) {
  std::random_device rd;  // Random device for seeding
  std::mt19937 gen(rd()); // Mersenne Twister engine
  std::bernoulli_distribution dist(0.5); // 50-50 distribution

  for (auto& value : signal) {
    value = dist(gen); // Set each value to a random boolean
  }
}

int main(int argc, char **argv)
{
  if (argc != 2) {
    std::cerr << "Usage: " << argv[0] << " <functional_vcd_filename>\n";
    return 1;
  }

  const std::string functional_vcd_filename = argv[1];

  constexpr int steps = 10;
  constexpr int number_timescale = 1;
  const std::string units_timescale = "us";
  gold_Inputs inputs;
  gold_Outputs outputs;
  gold_State state;
  gold_State next_state;

  std::ofstream vcd_file(functional_vcd_filename);

  vcd_file << "$timescale " << number_timescale << " " << units_timescale << " $end\n";
  vcd_file << "$scope module gold $end\n";
  {
    DumpHeader d(vcd_file);
    inputs.dump(d);
    outputs.dump(d);
    state.dump(d);
  }
  vcd_file << "$enddefinitions $end\n$dumpvars\n";
  vcd_file << "#0\n";
  // Set all signals to false
  for (int i = 0; i < inputs.size(); ++i) {
    auto input_variant = inputs.get_input(i);
    std::visit([](auto& signal_ref) {
      set_all_false(signal_ref.get());
    }, input_variant);
  }
     
  gold(inputs, outputs, state, next_state);
  {
    Dump d(vcd_file);
    inputs.dump(d);
    outputs.dump(d);
    state.dump(d);
  }
    
  for (int step = 0; step < steps; ++step) {
    // Functional backend cxx
    vcd_file << "#" << (step + 1) << "\n";
    // Set all signals to random
    for (int i = 0; i < inputs.size(); ++i) {
      auto input_variant = inputs.get_input(i);
      std::visit([](auto& signal_ref) {
	set_all_random(signal_ref.get());
      }, input_variant);
    }

    gold(inputs, outputs, state, next_state);
    {
      Dump d(vcd_file);
      inputs.dump(d);
      outputs.dump(d);
      state.dump(d);
    }
	
    state = next_state;
  }

  vcd_file.close();

  return 0;
}
