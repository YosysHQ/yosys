# perf-bisect agent

Playbook for running performance optimization work on this repo. This is the discipline that produced ~1.85× geomean speedup over upstream `main` across mec30k, mec60k, woc3k, and picorv32_x4.

For repo-level orientation (build, test, layout) see [`AGENTS.md`](../AGENTS.md). For the cumulative log of what's already been tried see [`benchmark-results/PERF-WORK-SUMMARY.md`](../benchmark-results/PERF-WORK-SUMMARY.md).

## When to use this agent

The user says one of:
- "Run an N-loop perf cycle on item X"
- "Tackle item N with the 5x loop strategy"
- "Profile <area> and optimize it"
- "Find a perf win in <pass>"

If the request is "make this faster" without a target, push back: ask what they've profiled or whether they want a profile-first cycle.

## The loop

A perf loop = one self-contained hypothesis, validated end-to-end before commit. Typical session is 5 loops; each produces either a commit or a documented negative result.

```
1. EXAMINE — read the code under hypothesis. Don't guess at structure.
2. HYPOTHESIZE — state in one sentence what you'll change and what speedup you expect.
3. EDIT — make ONE focused change. No bundled refactors. No drive-by cleanups.
4. BUILD — see "Build" in AGENTS.md. Standard `make yosys.exe` link will fail; use the response-file workflow.
5. BENCH — run the relevant subset of `benchmark-results/generated/*.ys` 5x. Take medians. Compare against pre-change baseline numbers.
6. TEST — at minimum, run the canary tests: `tests/various/{wreduce,wreduce2,peepopt,muxpack}.ys`. For changes touching opt passes also run `tests/opt`. For AST/genrtlil changes also run `tests/verilog`.
7. DECIDE — if real speedup AND tests pass → commit. If regression OR test failure → revert and write down why.
8. RECORD — append outcome (positive or negative) to the perf-loop history memory file.
```

## Build & test (perf-specific)

See [`AGENTS.md`](../AGENTS.md) for the standard build/test workflow. Perf-specific extras:

```bash
# Per-loop quick check — run the affected synthetic 5x
cd benchmark-results/generated
for i in 1 2 3 4 5; do
  { time ../../yosys.exe -q many_equiv_cells_60000.ys; } 2>&1 | grep real
done

# Full cycle (microbench + synthetic + default benchmarks, one label)
bash benchmark-results/run_loop.sh <label>

# Outputs:
#   benchmark-results/<label>-baseline-<date>.json
#   benchmark-results/<label>-synthetic-<date>.json
#   benchmark-results/hashlib-microbench-<label>-<date>.json
```

**Run-to-run variance is significant on Windows.** Apparent 1-4% wins frequently disappear with 10-rep verification. Take medians, run 5+ samples for any decision near the noise floor.

## Profiling pattern

When you don't know where time is spent, instrument with `<chrono>` and `fprintf(stderr, ...)`. **Revert the instrumentation before committing** — leave only the optimization in the final commit.

Pattern used to find the AST helper hot spot in `frontends/ast/ast.cc`:

```cpp
auto _t_start = std::chrono::steady_clock::now();
// ... code under measurement ...
auto _t_end = std::chrono::steady_clock::now();
auto us = [](auto a, auto b) {
    return std::chrono::duration_cast<std::chrono::microseconds>(b - a).count();
};
fprintf(stderr, "[my-prof] %s phase=%lldus n=%zu\n",
        identifier, (long long)us(_t_start, _t_end), count);
```

For passes that loop over modules, prefix output with the module name and counts so you can spot which module dominates.

## Anti-patterns (do NOT redo)

These have all been tried. Full reasoning in `benchmark-results/PERF-WORK-SUMMARY.md`.

1. **Changing hashtable iteration order** (e.g. Lemire bucket compression). Yosys `opt -fast` has order-fragile fixed-point loops that explode to 600k+ iterations.
2. **Adding fields to `entry_t`** (e.g. cached `udata_hash`). +4 bytes per entry hurts cache locality more than it saves work.
3. **`dict.reserve(N)` in mass-instantiated object ctors** (e.g. `Cell::parameters`). Memory cost per object dominates the rehash savings.
4. **Speculative loads in chain walks.** Chains are short at load factor 0.5; the load is wasted.
5. **AstNode arena allocators** (free-list or slab). Arena pollutes cache during opt passes; cell-heavy benchmarks regress 6-13%. Without a raw-pointer ownership refactor, `AstModule::ast` survivors across `design -reset/copy` create use-after-free.
6. **AST::process per-module parallelism.** Blocked by `log_assert(!Multithreading::active())` in IdString machinery. Architectural — not a perf change.
7. **PGO build.** +13–21% slower across all benchmarks with current training corpus.
8. **Hash-tag in `entry_t` for chain-walk filtering.** Exposes a latent invariant violation somewhere in pool/dict usage; deterministically crashes ~12 tests.
9. **Bulk `dict.count(k) ? dict.at(k)` → `find()` rewrite.** Compiler already CSEs the double lookup; manual rewrite regresses ~5% on woc3k.

## Patterns that work

1. **Early-bail audit.** For every pass with significant per-call setup (build SigMap, sigusers, mux_drivers, ConstEval seed, ModWalker), check whether the work-set is empty *before* doing the setup. A 5-line `if (...) continue;` at the top of `execute()` can be 30%+ on the right input.
2. **Per-Module generation-counter no-op cache.** Pattern (already in 8+ passes):
   ```cpp
   struct FooNoopCache { uint64_t generation; bool last_did_something; };
   static std::map<RTLIL::Module*, FooNoopCache> noop_cache;
   // per-module:
   auto it = noop_cache.find(module);
   if (it != noop_cache.end()
       && it->second.generation == module->generation
       && !it->second.last_did_something) continue;
   uint64_t gen_before = module->generation;
   // ... do work ...
   noop_cache[module] = {module->generation, module->generation != gen_before};
   ```
   Pointer reuse after `design -reset` is safe because each new Module gets a fresh global generation.
3. **Cache `data()` pointers across opaque calls.** Compiler can't prove the pointer is loop-invariant if the loop body calls user-defined comparators / hash functions.
4. **Hoist invariant work out of per-cell helpers.** When the same string/value is computed twice per call (e.g. `loc_string()` for both cell and wire in genrtlil helpers), hoist once and reuse.

## When to abort a loop early

Abort and document, don't push through:

- **Architectural blocker found** (e.g. `Multithreading::active()` assert prevents parallelism).
- **Test breakage you can't explain in <30 minutes.**
- **Bench delta within run-to-run noise after 5+ samples.**
- **Implementation requires rewriting the wrong part of the codebase** (e.g. `dict.reserve()` would need a separate codepath for transient vs persistent dicts).

A documented abort is more valuable than a speculative commit. The `benchmark-results/PERF-WORK-SUMMARY.md` "what didn't work" section is what stops the next agent from wasting cycles.

## Standard playbook for "tackle item N with the 5x loop strategy"

1. Read `benchmark-results/PERF-WORK-SUMMARY.md` and the perf-loop history memory file (if present) to confirm item N hasn't already been tried.
2. **Loop 1 = profiling/research, NOT a speculative edit.** Confirm the hot spot is where you think it is. If wrong, propose a pivot rather than burning the budget on a known-wrong target.
3. **Loops 2-4: implement, bench, refine.** ONE change per loop. Don't bundle.
4. **Loop 5: revert any instrumentation. Run full canary tests. Commit only if real improvement.**
5. **Final report:** numbers per loop, what landed, updated remaining-work list.

## Memory files

If running with Claude Code, the memory dir is `~/.claude/projects/C--Users-justi-Projects-yosys/memory/`. Relevant files:

- `MEMORY.md` — index of all memory files
- `build-and-test.md` — Windows/MSYS workflow notes
- `perf-loop-methodology.md` — concise version of this playbook
- `perf-loop-history.md` — cumulative log of every loop, what landed, what didn't
- `user-collab-style.md` — collaboration-style preferences

**Update `perf-loop-history.md` after each loop.** Single most valuable habit; stops the next session from retreading rejected ideas.
