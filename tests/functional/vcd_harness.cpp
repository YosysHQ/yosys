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
    constexpr int steps = 10;
    constexpr int number_timescale = 1;
    const std::string units_timescale = "us";
    my_module_Inputs inputs;
    my_module_Outputs outputs;
    my_module_State state;
    my_module_State next_state;

    std::ofstream vcd_file("functional_cxx.vcd");

    vcd_file << "$timescale " << number_timescale << " " << units_timescale << " $end\n"; //$scope module logic $end\n";
    {
        DumpHeader d(vcd_file);
        inputs.dump(d);
        outputs.dump(d);
        // vcd_file << "$scope module state $end\n";
        state.dump(d);
    }
    vcd_file << "$enddefinitions $end\n$dumpvars\n";

    cxxrtl_design::p_my__module top;

    // debug_items maps the hierarchical names of signals and memories in the design
    // to a cxxrtl_object (a value, a wire, or a memory)
    cxxrtl::debug_items all_debug_items;
    cxxrtl::debug_scope debug_scope;
    // Load the debug items of the top down the whole design hierarchy
    top.debug_info(&all_debug_items, nullptr, "");

    // vcd_writer is the CXXRTL object that's responsible for creating a string with
    // the VCD file contents.
    cxxrtl::vcd_writer vcd;
    vcd.timescale(number_timescale, units_timescale);

    // Here we tell the vcd writer to dump all the signals of the design, except for the
    // memories, to the VCD file.
    //
    // It's not necessary to load all debug objects to the VCD. There is, for example,
    // a  vcd.add(<debug items>, <filter>)) method which allows creating your custom filter to decide
    // what to add and what not.
    vcd.add_without_memories(all_debug_items);

    std::ofstream waves("cxxrtl.vcd");

    top.p_a.set<bool>(false);
    top.p_b.set<bool>(false);
    top.step();

    // We need to manually tell the VCD writer when to sample and write out the traced items.
    // This is only a slight inconvenience and allows for complete flexibility.
    // E.g. you could only start waveform tracing when an internal signal has reached some specific
    // value etc.
    vcd.sample(0);
    vcd_file << "#0\n";
    inputs.a = $const<1>(false);
    inputs.b = $const<1>(false);
    {
        Dump d(vcd_file);
        inputs.dump(d);
        outputs.dump(d);
        state.dump(d);
    }

    // Initialize random number generator
    std::random_device rd;
    std::mt19937 gen(rd());
    std::bernoulli_distribution dist(0.5); // 50% chance for true or false
    
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
