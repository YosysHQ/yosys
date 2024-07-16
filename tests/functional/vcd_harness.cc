#include <cstdio>
#include <iostream>
#include <fstream>
#include <random>
#include <ctype.h>
#include <vector>

#include "my_module_functional_cxx.cc"

std::string vcd_name_mangle(std::string name) {
  std::string ret = name;
  bool escape = ret.empty() || !isalpha(ret[0]) && ret[0] != '_';
  for(size_t i = 0; i < ret.size(); i++) {
    if(isspace(ret[i])) ret[i] = '_';
    if(!isalnum(ret[i]) && ret[i] != '_' && ret[i] != '$')
      escape = true;
  }
  if(escape)
    return "\\" + ret;
  else
    return ret;
}
std::unordered_map<std::string, std::string> codes; 

struct DumpHeader {
  std::ofstream &ofs;
  std::string code = "!";
  DumpHeader(std::ofstream &ofs) : ofs(ofs) {}
  void increment_code() {
    for(size_t i = 0; i < code.size(); i++)
      if(code[i]++ == '~')
        code[i] = '!';
      else
        return;
    code.push_back('!');
  }
  template <size_t n>
  void operator()(const char *name, Signal<n> value) {
    ofs << "$var wire " << n << " " << code << " " << vcd_name_mangle(name) << " $end\n";
    codes[name] = code;
    increment_code();
  }
  template <size_t n, size_t m>
  void operator()(const char *name, Memory<n, m> value) {
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
      ofs << codes[name] << "\n";
      return;
    }
    // vector (multi-bit) signals
    ofs << "b";
    for (size_t i = n; i-- > 0;)
      ofs << (value[i] ? '1' : '0');
    ofs << " " << codes[name] << "\n";
  }
  template <size_t n, size_t m>
  void operator()(const char *name, Memory<n, m> value) {
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
  if (argc != 4) {
    std::cerr << "Usage: " << argv[0] << " <functional_vcd_filename> <steps> <seed>\n";
    return 1;
  }

  const std::string functional_vcd_filename = argv[1];
  const int steps = atoi(argv[2]);
  const uint32_t seed = atoi(argv[3]);

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
  std::mt19937 gen(seed);

  inputs.visit(Reset());

  for (int step = 0; step < steps; ++step) {
    vcd_file << "#" << step << "\n";
    gold::eval(inputs, outputs, state, next_state);
    {
      Dump d(vcd_file);
      inputs.visit(d);
      outputs.visit(d);
      state.visit(d);
    }

    state = next_state;
    inputs.visit(Randomize(gen));
  }

  vcd_file.close();

  return 0;
}
