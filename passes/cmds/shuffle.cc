#include "kernel/yosys.h"
#include <random>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// Fisher–Yates shuffle
// https://en.wikipedia.org/wiki/Fisher%E2%80%93Yates_shuffle
template<typename T>
static void shuffle_vector(std::vector<T> &vec, std::mt19937 &rng)
{
	for (size_t i = vec.size(); i > 1; i--)
		std::swap(vec[i-1], vec[rng() % i]);
}

template<typename K, typename T>
static void shuffle_dict(dict<K, T> &d, std::mt19937 &rng)
{
	std::vector<std::pair<K, T>> entries(d.begin(), d.end());
	shuffle_vector(entries, rng);
	dict<K, T> shuffled;
	for (auto &entry : entries)
		shuffled.insert(std::move(entry));
	d.swap(shuffled);
}

struct ShufflePass : public Pass {
	ShufflePass() : Pass("shuffle", "deterministically reorder design objects") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    shuffle [-seed <seed>] [selection]\n");
		log("\n");
		log("Deterministically reorder design objects.\n");
		log("\n");
		log("    -seed <seed>\n");
		log("        use the given random number generator seed (default: 1)\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		unsigned int seed = 1;

		log_header(design, "Executing SHUFFLE pass (deterministically reorder design objects).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-seed" && argidx+1 < args.size()) {
				seed = std::stoul(args[++argidx]);
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		std::mt19937 rng(seed);

		for (auto module : design->selected_whole_modules_warn())
		{
			log("Shuffling module %s.\n", module);
			shuffle_dict(module->wires_, rng);
			shuffle_dict(module->cells_, rng);
			shuffle_vector(module->connections_, rng);
			shuffle_dict(module->memories, rng);
			shuffle_dict(module->processes, rng);
		}
	}
} ShufflePass;

PRIVATE_NAMESPACE_END
