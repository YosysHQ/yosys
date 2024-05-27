#include <cstdio>
#include <iostream>
#include <fstream>
#include <random>

#include <cxxrtl/cxxrtl_vcd.h>

#include "my_module_cxxrtl.cc"
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

int main(int argc, char **argv)
{
    if (argc != 3) {
        std::cerr << "Usage: " << argv[0] << " <functional_vcd_filename> <cxxrtl_vcd_filename>\n";
        return 1;
    }

    const std::string functional_vcd_filename = argv[1];
    const std::string cxxrtl_vcd_filename = argv[2];

    constexpr int steps = 10;
    constexpr int number_timescale = 1;
    const std::string units_timescale = "us";
    my_module_Inputs inputs;
    my_module_Outputs outputs;
    my_module_State state;
    my_module_State next_state;

    std::ofstream vcd_file(functional_vcd_filename);

    vcd_file << "$timescale " << number_timescale << " " << units_timescale << " $end\n";
    {
        DumpHeader d(vcd_file);
        inputs.dump(d);
        outputs.dump(d);
        state.dump(d);
    }
    vcd_file << "$enddefinitions $end\n$dumpvars\n";

    cxxrtl_design::p_my__module top;

    cxxrtl::debug_items all_debug_items;
    cxxrtl::debug_scope debug_scope;
    top.debug_info(&all_debug_items, nullptr, "");

    cxxrtl::vcd_writer vcd;
    vcd.timescale(number_timescale, units_timescale);
    vcd.add_without_memories(all_debug_items);

    std::ofstream waves(cxxrtl_vcd_filename);

    top.p_a.set<bool>(false);
    top.p_b.set<bool>(false);
    top.step();

    vcd.sample(0);
    vcd_file << "#0\n";
    inputs.a = $const<1>(false);
    inputs.b = $const<1>(false);
    my_module(inputs, outputs, state, next_state);
    {
      Dump d(vcd_file);
      inputs.dump(d);
      outputs.dump(d);
      state.dump(d);
    }
    
    std::random_device rd;
    std::mt19937 gen(rd());
    std::bernoulli_distribution dist(0.5);

    for (int step = 0; step < steps; ++step) {
        const bool a_value = dist(gen);
        const bool b_value = dist(gen);

        // cxxrtl
        top.p_a.set<bool>(a_value);
        top.p_b.set<bool>(b_value);
        top.step();
        vcd.sample(step + 1);

        waves << vcd.buffer;
        vcd.buffer.clear();

        // Functional backend cxx
        vcd_file << "#" << (step + 1) << "\n";
        inputs.a = $const<1>(a_value);
        inputs.b = $const<1>(b_value);
	
        my_module(inputs, outputs, state, next_state);
        {
            Dump d(vcd_file);
            inputs.dump(d);
            outputs.dump(d);
            state.dump(d);
        }
	
        state = next_state;
    }

    vcd_file.close();
    waves.close();

    return 0;
}
