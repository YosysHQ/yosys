#ifndef RTLIL_HELPERS_H
#define RTLIL_HELPERS_H

#include <gtest/gtest.h>

#include "kernel/rtlil.h"

YOSYS_NAMESPACE_BEGIN

class SigSpecRepTest : public ::testing::Test {
protected:
	Design* d;
	Module* m;

	void SetUp() override {
		d = new Design;
		m = d->addModule("$test");
	}

	void TearDown() override {
		delete d;
	}

	// Create n wires with given width
	std::vector<Wire*> createWires(int count, int width = 4) {
		std::vector<Wire*> wires;
		for (int i = 0; i < count; i++) {
			Wire* w = m->addWire(stringf("$w%d", i), width);
			wires.push_back(w);
		}
		return wires;
	}

	// Append all wires to a SigSpec
	SigSpec wiresAsSigSpec(const std::vector<Wire*>& wires) {
		SigSpec sig;
		for (auto w : wires)
			sig.append(w);
		return sig;
	}

	// Create a SigSpec of constants
	SigSpec constsAsSigSpec(int count, int width = 4) {
		SigSpec sig;
		for (int i = 0; i < count; i++)
			sig.append(Const(i, width));
		return sig;
	}

	// Convert wires to pool of SigBits
	pool<SigBit> wiresToPool(const std::vector<Wire*>& wires) {
		pool<SigBit> pool;
		for (auto w : wires)
			for (auto &bit : SigSpec(w))
				pool.insert(bit);
		return pool;
	}

	// Convert wires to set of SigBits
	std::set<SigBit> wiresToSet(const std::vector<Wire*>& wires) {
		std::set<SigBit> set;
		for (auto w : wires)
			for (auto &bit : SigSpec(w))
				set.insert(bit);
		return set;
	}
};

YOSYS_NAMESPACE_END

#endif /* RTLIL_HELPERS_H */
