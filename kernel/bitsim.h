#ifndef BITSIM_H
#define BITSIM_H

#include "kernel/modtools.h"

YOSYS_NAMESPACE_BEGIN

struct BitSim {
	Module *module;
	SigMap &sigmap;
	ModWalker &modwalker;
	dict<SigBit, uint64_t> sim_vals;
	uint64_t rng_state;

	BitSim(Module *m, SigMap &sm, ModWalker &mw) 
		: module(m), sigmap(sm), modwalker(mw), rng_state(1337) {}

	uint64_t next_rand() {
		uint32_t lo = mkhash_xorshift((uint32_t)rng_state);
		uint32_t hi = mkhash_xorshift((uint32_t)(rng_state >> 32) ^ lo);
		rng_state = ((uint64_t)hi << 32) | lo;
		return rng_state;
	}

	uint64_t eval_bit(SigBit b) {
		SigBit mapped = sigmap(b);
		if (mapped == State::S0) return 0ULL;
		if (mapped == State::S1) return ~0ULL;
		if (mapped == State::Sx || mapped == State::Sz) return 0ULL;

		auto it = sim_vals.find(mapped);
		if (it != sim_vals.end()) return it->second;
		sim_vals[mapped] = 0; 
		uint64_t res = 0;

		if (!modwalker.has_drivers(mapped)) {
			res = next_rand();
		} else {
			auto &drivers = modwalker.signal_drivers[mapped];
			if (drivers.empty()) {
				res = next_rand();
			} else {
				auto driver = *drivers.begin();
				Cell *cell = driver.cell;
				
				if (cell->is_builtin_ff()) {
					res = next_rand();
				} else if (cell->type == ID($_AND_)) {
					res = eval_bit(cell->getPort(ID::A)[0]) & eval_bit(cell->getPort(ID::B)[0]);
				} else if (cell->type == ID($_OR_)) {
					res = eval_bit(cell->getPort(ID::A)[0]) | eval_bit(cell->getPort(ID::B)[0]);
				} else if (cell->type == ID($_XOR_)) {
					res = eval_bit(cell->getPort(ID::A)[0]) ^ eval_bit(cell->getPort(ID::B)[0]);
				} else if (cell->type == ID($_NOT_)) {
					res = ~eval_bit(cell->getPort(ID::A)[0]);
				} else if (cell->type == ID($_MUX_)) {
					uint64_t s = eval_bit(cell->getPort(ID::S)[0]);
					uint64_t a = eval_bit(cell->getPort(ID::A)[0]);
					uint64_t b = eval_bit(cell->getPort(ID::B)[0]);
					res = (a & ~s) | (b & s);
				} else if (cell->type == ID($mux)) {
					uint64_t s = eval_bit(cell->getPort(ID::S)[0]);
					uint64_t a = eval_bit(cell->getPort(ID::A)[driver.offset]);
					uint64_t b = eval_bit(cell->getPort(ID::B)[driver.offset]);
					res = (a & ~s) | (b & s);
				} else {
					res = next_rand();
				}
			}
		}
		
		sim_vals[mapped] = res;
		return res;
	}
};

YOSYS_NAMESPACE_END

#endif
