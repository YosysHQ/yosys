#include <cstdio>
#include <iostream>
#include <fstream>
#include <random>
#include <ctype.h>
#include <vector>
#include <unordered_map>

#include "my_module_functional_cxx.cc"

class VcdFile {
	std::ofstream &ofs;
	std::string code_alloc = "!";
	std::unordered_map<std::string, std::string> codes;
	std::string name_mangle(std::string name) {
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
	std::string allocate_code() {
		std::string ret = code_alloc;
		for (size_t i = 0; i < code_alloc.size(); i++)
			if (code_alloc[i]++ == '~')
				code_alloc[i] = '!';
			else
				return ret;
		code_alloc.push_back('!');
		return ret;
	}
public:
	VcdFile(std::ofstream &ofs) : ofs(ofs) {}
	struct DumpHeader {
		VcdFile *file;
		explicit DumpHeader(VcdFile *file) : file(file) {}
		template <size_t n> void operator()(const char *name, Signal<n> value)
		{
			auto it = file->codes.find(name);
			if(it == file->codes.end())
				it = file->codes.emplace(name, file->allocate_code()).first;
			file->ofs << "$var wire " << n << " " << it->second << " " << file->name_mangle(name) << " $end\n";
		}
		template <size_t n, size_t m> void operator()(const char *name, Memory<n, m> value) {}
	};
	struct Dump {
		VcdFile *file;
		explicit Dump(VcdFile *file) : file(file) {}
		template <size_t n> void operator()(const char *name, Signal<n> value)
		{
			if (n == 1) {
				file->ofs << (value[0] ? '1' : '0');
				file->ofs << file->codes.at(name) << "\n";
			} else {
				file->ofs << "b";
				for (size_t i = n; i-- > 0;)
					file->ofs << (value[i] ? '1' : '0');
				file->ofs << " " << file->codes.at(name) << "\n";
			}
		}
		template <size_t n, size_t m> void operator()(const char *name, Memory<n, m> value) {}
	};
	void begin_header() {
		constexpr int number_timescale = 1;
		const std::string units_timescale = "us";
		ofs << "$timescale " << number_timescale << " " << units_timescale << " $end\n";
		ofs << "$scope module gold $end\n";
	}
	void end_header() {
		ofs << "$enddefinitions $end\n$dumpvars\n";
	}
	template<typename... Args> void header(Args ...args) {
		begin_header();
		DumpHeader d(this);
		(args.visit(d), ...);
		end_header();
	}
	void begin_data(int step) {
		ofs << "#" << step << "\n";
	}
	template<typename... Args> void data(int step, Args ...args) {
		begin_data(step);
		Dump d(this);
		(args.visit(d), ...);
	}
	DumpHeader dump_header() { return DumpHeader(this); }
	Dump dump() { return Dump(this); }
};

template <size_t n> Signal<n> random_signal(std::mt19937 &gen)
{
	std::uniform_int_distribution<uint32_t> dist;
	std::array<uint32_t, (n + 31) / 32> words;
	for (auto &w : words)
		w = dist(gen);
	return Signal<n>::from_array(words);
}

struct Randomize {
	std::mt19937 &gen;
	Randomize(std::mt19937 &gen) : gen(gen) {}

	template <size_t n> void operator()(const char *, Signal<n> &signal) { signal = random_signal<n>(gen); }
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

	gold::Inputs inputs;
	gold::Outputs outputs;
	gold::State state;
	gold::State next_state;

	std::ofstream vcd_file(functional_vcd_filename);
	VcdFile vcd(vcd_file);
	vcd.header(inputs, outputs, state);

	std::mt19937 gen(seed);

	gold::initialize(state);

	for (int step = 0; step < steps; ++step) {
		inputs.visit(Randomize(gen));

		gold::eval(inputs, outputs, state, next_state);
		vcd.data(step, inputs, outputs, state);

		state = next_state;
	}

	return 0;
}
