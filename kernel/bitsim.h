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

	uint64_t xorshift64() {
		rng_state ^= rng_state << 13;
		rng_state ^= rng_state >> 7;
		rng_state ^= rng_state << 17;
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
			res = xorshift64();
		} else {
			auto &drivers = modwalker.signal_drivers[mapped];
			if (drivers.empty()) {
				res = xorshift64();
			} else {
				auto driver = *drivers.begin();
				Cell *cell = driver.cell;
				
				if (cell->is_builtin_ff()) {
					res = xorshift64();
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
					res = xorshift64();
				}
			}
		}
		
		sim_vals[mapped] = res;
		return res;
	}
};

YOSYS_NAMESPACE_END

#endif
