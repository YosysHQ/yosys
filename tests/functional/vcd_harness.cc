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

template<size_t n>
Signal<n> random_signal(std::mt19937 &gen) {
  std::uniform_int_distribution<uint32_t> dist;
  std::array<uint32_t, (n+31)/32> words;
  for(auto &w : words)
    w = dist(gen);
  return Signal<n>::from_array(words);
}

struct Reset {
  template <size_t n>
  void operator()(const char *, Signal<n> &signal) {
    signal = 0;
  }
};

struct Randomize {
  std::mt19937 &gen;
  Randomize(std::mt19937 &gen) : gen(gen) {}

  template <size_t n>
  void operator()(const char *, Signal<n> &signal) {
    signal = random_signal<n>(gen);
  }
};

int main(int argc, char **argv)
{
  if (argc != 2) {
    std::cerr << "Usage: " << argv[0] << " <functional_vcd_filename>\n";
    return 1;
  }

  const std::string functional_vcd_filename = argv[1];

  constexpr int steps = 1000;
  constexpr int number_timescale = 1;
  const std::string units_timescale = "us";
  gold::Inputs inputs;
  gold::Outputs outputs;
  gold::State state;
  gold::State next_state;

  std::ofstream vcd_file(functional_vcd_filename);

  vcd_file << "$timescale " << number_timescale << " " << units_timescale << " $end\n";
  vcd_file << "$scope module gold $end\n";
  {
    DumpHeader d(vcd_file);
    inputs.visit(d);
    outputs.visit(d);
    state.visit(d);
  }
  vcd_file << "$enddefinitions $end\n$dumpvars\n";
  vcd_file << "#0\n";
  // Set all signals to false
  inputs.visit(Reset());

  gold::eval(inputs, outputs, state, next_state);
  {
    Dump d(vcd_file);
    inputs.visit(d);
    outputs.visit(d);
    state.visit(d);
  }

  // Initialize random number generator once
  std::random_device rd;
  std::mt19937 gen(rd());

  for (int step = 0; step < steps; ++step) {
    // Functional backend cxx
    vcd_file << "#" << (step + 1) << "\n";
    inputs.visit(Randomize(gen));

    gold::eval(inputs, outputs, state, next_state);
    {
      Dump d(vcd_file);
      inputs.visit(d);
      outputs.visit(d);
      state.visit(d);
    }

    state = next_state;
  }

  vcd_file.close();

  return 0;
}
