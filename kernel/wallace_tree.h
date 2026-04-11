/**
 * Wallace tree utilities for multi-operand addition using carry-save adders
 *
 * Terminology:
 * - compressor: $fa viewed as reducing 3 inputs to 2 outputs (sum + shifted carry) (3:2 compressor)
 * - level:      A stage of parallel compression operations
 * - depth:      Maximum number of 3:2 compressor levels from any input to a signal
 *
 * References:
 * - "Binary Adder Architectures for Cell-Based VLSI and their Synthesis" (https://iis-people.ee.ethz.ch/~zimmi/publications/adder_arch.pdf)
 * - "A Suggestion for a Fast Multiplier" (https://www.ece.ucdavis.edu/~vojin/CLASSES/EEC280/Web-page/papers/Arithmetic/Wallace_mult.pdf)
 */

#ifndef WALLACE_TREE_H
#define WALLACE_TREE_H

#include "kernel/sigtools.h"
#include "kernel/yosys.h"

YOSYS_NAMESPACE_BEGIN

inline std::pair<SigSpec, SigSpec> emit_fa(Module *module, SigSpec a, SigSpec b, SigSpec c, int width)
{
	SigSpec sum = module->addWire(NEW_ID, width);
	SigSpec cout = module->addWire(NEW_ID, width);

	module->addFa(NEW_ID, a, b, c, cout, sum);

	SigSpec carry;
	carry.append(State::S0);
	carry.append(cout.extract(0, width - 1));
	return {sum, carry};
}

/**
 * wallace_reduce_scheduled() - Reduce multiple operands to two using a Wallace tree
 * @module: The Yosys module to which the compressors will be added
 * @sigs: Vector of input signals (operands) to be reduced
 * @width: Target bit-width to which all operands will be zero-extended
 * @compressor_count: Optional pointer to return the number of $fa cells emitted
 *
 * Return: The final two reduced operands, that are to be fed into an adder
 */
inline std::pair<SigSpec, SigSpec> wallace_reduce_scheduled(Module *module, std::vector<SigSpec> &sigs, int width, int *compressor_count = nullptr)
{
	struct DepthSig {
		SigSpec sig;
		int depth;
	};

	for (auto &s : sigs)
		s.extend_u0(width);

	std::vector<DepthSig> operands;
	operands.reserve(sigs.size());
	for (auto &s : sigs)
		operands.push_back({s, 0});

	// Number of $fa's emitted
	if (compressor_count)
		*compressor_count = 0;

	// Only compress operands ready at current level
	for (int level = 0; operands.size() > 2; level++) {
		// Partition operands into ready and waiting
		std::vector<DepthSig> ready, waiting;
		for (auto &op : operands) {
			if (op.depth <= level)
				ready.push_back(op);
			else
				waiting.push_back(op);
		}

		if (ready.size() < 3)
			continue;

		// Apply compressors to ready operands
		std::vector<DepthSig> compressed;
		size_t i = 0;
		while (i + 2 < ready.size()) {
			auto [sum, carry] = emit_fa(module, ready[i].sig, ready[i + 1].sig, ready[i + 2].sig, width);
			int new_depth = std::max({ready[i].depth, ready[i + 1].depth, ready[i + 2].depth}) + 1;
			compressed.push_back({sum, new_depth});
			compressed.push_back({carry, new_depth});
			if (compressor_count)
				(*compressor_count)++;
			i += 3;
		}
		// Uncompressed operands pass through to next level
		for (; i < ready.size(); i++)
			compressed.push_back(ready[i]);
		// Merge compressed with waiting operands
		for (auto &op : waiting)
			compressed.push_back(op);

		operands = std::move(compressed);
	}

	if (operands.size() == 0)
		return {SigSpec(State::S0, width), SigSpec(State::S0, width)};
	else if (operands.size() == 1)
		return {operands[0].sig, SigSpec(State::S0, width)};
	else {
		log_assert(operands.size() == 2);
		log("    Wallace tree depth: %d levels of $fa + 1 final $add\n", std::max(operands[0].depth, operands[1].depth));
		return {operands[0].sig, operands[1].sig};
	}
}

YOSYS_NAMESPACE_END

#endif
