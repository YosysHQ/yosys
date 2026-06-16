/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Inspect the design-level twine pool that backs src-attribute interning.
 */

#include "kernel/register.h"
#include "kernel/rtlil.h"
#include "kernel/twine.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct DumpTwinesPass : public Pass {
	DumpTwinesPass() : Pass("dump_twines", "dump the design-level src twine pool") { }

	void help() override
	{
		log("\n");
		log("    dump_twines [-flat]\n");
		log("\n");
		log("Print every node in design->twines. Leaves show the literal\n");
		log("path:line.col string, concats show their child id list. With\n");
		log("-flat each concat is additionally rendered as the pipe-joined\n");
		log("flat string a backend would emit.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		bool flat = false;
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-flat") {
				flat = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		const TwinePool &pool = design->twines;
		log("twine pool: %zu local nodes\n", pool.size());
		for (auto it = pool.backing.begin(); it != pool.backing.end(); ++it) {
			TwineRef id = STATIC_TWINE_END + pool.backing.get_index(it);
			const Twine &n = *it;
			if (n.is_leaf()) {
				log("  @%zu leaf \"%s\"", (size_t)id, n.leaf().c_str());
			} else if (n.is_suffix()) {
				log("  @%zu suffix @%zu + \"%s\"", (size_t)id,
						(size_t)n.suffix().prefix, n.suffix().tail.c_str());
			} else if (n.is_concat()) {
				std::string children;
				for (TwineRef c : n.children()) {
					if (!children.empty())
						children += ", ";
					children += "@" + std::to_string((size_t)c);
				}
				log("  @%zu concat [%s]", (size_t)id, children.c_str());
			} else {
				log("  @%zu dead", (size_t)id);
			}
			if (flat)
				log(" -> \"%s\"", pool.str(id).c_str());
			log("\n");
		}
	}
} DumpTwinesPass;

struct GcTwinesPass : public Pass {
	GcTwinesPass() : Pass("gc_twines", "reap unreferenced entries from the src twine pool") { }

	void help() override
	{
		log("\n");
		log("    gc_twines\n");
		log("\n");
		log("Walk the design, collect every \"@N\" referenced by any cell, wire,\n");
		log("module, memory, or process attribute, and rebuild design->twines\n");
		log("to contain only those entries plus their transitive leaf children.\n");
		log("Cell src attributes are rewritten in place via the resulting id\n");
		log("remap, so the design is unchanged at the path:line.col layer.\n");
		log("\n");
		log("Useful after long opt_merge / techmap runs that leave intermediate\n");
		log("concat nodes orphaned: each merge step splices a previous concat's\n");
		log("leaves into the new node (the flatten invariant), so the prior\n");
		log("concat becomes unreferenced as soon as the surviving cell's src is\n");
		log("rewritten.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		extra_args(args, 1, design);
		size_t before = design->twines.size();
		size_t freed = design->gc_twines();
		log("twine gc: %zu nodes -> %zu (%zu freed)\n",
				before, design->twines.size(), freed);
	}
} GcTwinesPass;

PRIVATE_NAMESPACE_END
