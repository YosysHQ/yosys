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
		log("twine pool: %zu nodes (%zu leaves, %zu suffixes, %zu concats)\n",
				pool.size(), pool.leaf_count(), pool.suffix_count(), pool.concat_count());
		pool.for_each_live([&](Twine::Id id, const Twine &n) {
			if (n.is_leaf()) {
				log("  @%u leaf rc=%u %s\n", id, pool.refcount(id), n.leaf().c_str());
			} else if (n.is_suffix()) {
				if (flat) {
					log("  @%u suffix rc=%u @%u + %s -> %s\n", id, pool.refcount(id),
							n.suffix().parent, n.suffix().tail.c_str(),
							pool.flat_string(id).c_str());
				} else {
					log("  @%u suffix rc=%u @%u + %s\n", id, pool.refcount(id),
							n.suffix().parent, n.suffix().tail.c_str());
				}
			} else {
				std::string children;
				for (Twine::Id c : n.children()) {
					if (!children.empty())
						children += ", ";
					children += "@" + std::to_string(c);
				}
				if (flat) {
					log("  @%u concat rc=%u [%s] -> %s\n", id, pool.refcount(id),
							children.c_str(), pool.flatten(id).c_str());
				} else {
					log("  @%u concat rc=%u [%s]\n", id, pool.refcount(id),
							children.c_str());
				}
			}
		});
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
