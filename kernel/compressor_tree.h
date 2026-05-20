/**
 * Generalized compressor-tree utilities for multi-operand addition
 *
 * Terminology:
 * - compressor: $fa viewed as reducing N inputs to M outputs (sum + shifted carry) (N:M compressor)
 * - level:      A stage of parallel compression operations
 * - depth:      Maximum number of N:M compressor levels from any input to a signal
 *
 * Supported compressors:
 * - 3:2 compressor
 * - 4:2 compressor
 *
 * References:
 * - "Some schemes for parallel multipliers" (https://www.acsel-lab.com/arithmetic/arith6/papers/ARITH6_Dadda.pdf)
 * - "Binary Adder Architectures for Cell-Based VLSI" (https://iis-people.ee.ethz.ch/~zimmi/publications/adder_arch.pdf)
 * - "Basilisk: Achieving Competitive Performance with Open EDA Tools" (https://arxiv.org/pdf/2405.03523)
 * - "Binary Adder Architectures for Cell-Based VLSI and their Synthesis" (https://iis-people.ee.ethz.ch/~zimmi/publications/adder_arch.pdf)
 * - "A Suggestion for a Fast Multiplier" (https://www.ece.ucdavis.edu/~vojin/CLASSES/EEC280/Web-page/papers/Arithmetic/Wallace_mult.pdf)
 */

#ifndef COMPRESSOR_TREE_H
#define COMPRESSOR_TREE_H

#include "kernel/sigtools.h"
#include "kernel/yosys.h"

YOSYS_NAMESPACE_BEGIN

namespace CompressorTree
{

// Width threshold below which a ripple is preferred over parallel-prefix
constexpr int RIPPLE_PREFIX_THRESHOLD = 16;

enum class Strategy {
	FA_ONLY,   // 3:2 compressors
	PREFER_42, // Prefer 4:2 grouping when >=4 operands ready
	DADDA,     // Defer compression until column counts exceed
};

struct DepthSig {
	SigSpec sig;
	int depth;
};

enum class FinalAdder {
	DEFAULT,         // emit $add and let downstream techmap pick
	RIPPLE,          // emit $add with explicit narrow hint
	PARALLEL_PREFIX, // emit $add with PARALLEL_PREFIX
	ELARITH_MOP_CSV, // black-box instance of \AddMopCsv
};

enum class FinalMode {
	AUTO,
	RIPPLE,
	PREFIX,
	ELARITH
};

inline std::pair<SigSpec, SigSpec> emit_compressor_32(Module *module, SigSpec a, SigSpec b, SigSpec c, int width)
{
	SigSpec sum = module->addWire(NEW_ID, width);
	SigSpec cout = module->addWire(NEW_ID, width);
	module->addFa(NEW_ID, a, b, c, cout, sum);

	SigSpec carry;
	carry.append(State::S0);
	carry.append(cout.extract(0, width - 1));
	return {sum, carry};
}

inline std::pair<SigSpec, SigSpec> emit_compressor_42(Module *module, SigSpec a, SigSpec b, SigSpec c, SigSpec d, int width)
{
	// First FA: a + b + c -> s0
	SigSpec s0 = module->addWire(NEW_ID, width);
	SigSpec cout_h_full = module->addWire(NEW_ID, width);
	module->addFa(NEW_ID, a, b, c, cout_h_full, s0);

	// cin[0] = 0, cin[i] = cout_h_full[i-1]
	SigSpec cin;
	cin.append(State::S0);
	if (width > 1)
		cin.append(cout_h_full.extract(0, width - 1));

	// Second FA: s0 + d + cin -> sum
	SigSpec sum = module->addWire(NEW_ID, width);
	SigSpec carry_full = module->addWire(NEW_ID, width);
	module->addFa(NEW_ID, s0, d, cin, carry_full, sum);

	SigSpec carry;
	carry.append(State::S0);
	if (width > 1)
		carry.append(carry_full.extract(0, width - 1));

	return {sum, carry};
}

inline SigSpec normalize_to_width(SigSpec sig, bool is_signed, int width)
{
	// Zero/sign-extend to width
	if (GetSize(sig) < width) {
		SigBit pad;
		if (is_signed && GetSize(sig) > 0)
			pad = sig[GetSize(sig) - 1];
		else
			pad = State::S0;
		sig.append(SigSpec(pad, width - GetSize(sig)));
	}
	// Truncate to width
	if (GetSize(sig) > width)
		sig = sig.extract(0, width);
	return sig;
}

/**
 * generate_partial_products() - Generate partial products for FMA concat
 * @module:The Yosys module to which the compressors will be added
 * @a: Signal A
 * @b: Signal B
 * @a_signed: Whether signal A is signed
 * @b_signed: Whether signal B is signed
 * @width: Target width
 *
 * Return: Partial-product matrix as a set of depth-0 vectors
 */
inline std::vector<DepthSig> generate_partial_products(Module *module, SigSpec a, SigSpec b, bool a_signed, bool b_signed, int width) {
	int width_a = GetSize(a);
	int width_b = GetSize(b);
	std::vector<DepthSig> products;
	products.reserve(width_a + 3);

	for (int i = 0; i < width_a; i++) {
		SigBit ai = a[i];

		// b_shifted = (0_i ## b)
		SigSpec b_shifted = SigSpec(State::S0, i);
		b_shifted.append(b);
		b_shifted = normalize_to_width(b_shifted, false, width);

		// row = b_shifted & replicate(a[i], width)
		SigSpec ai_rep = SigSpec(ai, width);
		SigSpec row = module->addWire(NEW_ID, width);
		module->addAnd(NEW_ID, b_shifted, ai_rep, row);

		// Apply Modified Baugh-Wooley inversions for this row
		bool row_is_bottom = (i == width_a - 1);
		bool any_inversion = (row_is_bottom && b_signed) || a_signed;

		if (any_inversion) {
			std::vector<RTLIL::State> mask(width, RTLIL::State::S0);

			for (int j = 0; j < width_b; j++) {
				int col = i + j;
				if (col < 0 || col >= width)
					continue;
				bool col_is_right = (j == width_b - 1);
				// Flip masks
				bool invert = (row_is_bottom && b_signed) ^ (col_is_right && a_signed);
				if (invert)
					mask[col] = RTLIL::State::S1;
			}

			// Skip the xor entirely if the mask is all zeroes
			bool nonzero = false;
			for (auto s : mask)
				if (s == RTLIL::State::S1) {
					nonzero = true;
					break;
				}
			if (nonzero) {
				SigSpec inverted = module->addWire(NEW_ID, width);
				module->addXor(NEW_ID, row, SigSpec(RTLIL::Const(mask)), inverted);
				row = inverted;
			}
		}

		products.push_back({row, 0});
	}

	// Correction constants
	auto push_one_at = [&](int col) {
		if (col < 0 || col >= width) 
			return;
		std::vector<RTLIL::State> v(width, RTLIL::State::S0);
		v[col] = RTLIL::State::S1;
		products.push_back({SigSpec(RTLIL::Const(v)), 0});
	};

	if (b_signed)
		push_one_at(width_a - 1);
	if (a_signed)
		push_one_at(width_b - 1);
	if (a_signed || b_signed)
		push_one_at(width_a + width_b - 1);

	return products;
}

/**
 * reduce_scheduled() - Reduce multiple operands to two using a compressor tree
 * @module: The Yosys module to which the compressors will be added
 * @operands: Vector of operands to be reduced
 * @sigs: Vector of input signals (operands) to be reduced
 * @width: Target bit-width to which all operands will be zero-extended
 * @strategy: Compression strategy to use
 * @compressor_count: Optional pointer to return the number of $fa cells emitted
 *
 * Return: The final two reduced operands, that are to be fed into an adder
 */
inline std::pair<SigSpec, SigSpec> reduce_scheduled(Module *module, std::vector<DepthSig> operands, int width, Strategy strategy, int *compressor_count = nullptr) {
	int levels = 0;
	int fa_count = 0;
	int c42_count = 0;
	int final_depth = 0;

	for (auto &op : operands)
		op.sig.extend_u0(width);

	// Only compress operands ready at current level
	for (int level = 0; operands.size() > 2; level++) {
		// Partition operands into ready and waiting
		std::vector<DepthSig> ready;
		std::vector<DepthSig> waiting;
		ready.reserve(operands.size());
		for (auto &op : operands) {
			if (op.depth <= level)
				ready.push_back(op);
			else
				waiting.push_back(op);
		}

		if (ready.size() < 3) {
			levels++;
			continue;
		}

		// Apply compressors to ready operands
		std::vector<DepthSig> compressed;
		compressed.reserve(ready.size());
		size_t i = 0;

		// PREFER_42 attempts 4:2 grouping greedily (falls back to 3:2 for the residual)
		// FA_ONLY skips
		// DADDA = PREFER_42 (TODO: inspect column heights?)
		bool try_42 = (strategy == Strategy::PREFER_42 || strategy == Strategy::DADDA);

		while (i < ready.size()) {
			size_t remaining = ready.size() - i;

			if (try_42 && remaining >= 4) {
				DepthSig a = ready[i + 0];
				DepthSig b = ready[i + 1];
				DepthSig c = ready[i + 2];
				DepthSig d = ready[i + 3];

				auto [sum, carry] = emit_compressor_42(module, a.sig, b.sig, c.sig, d.sig, width);
				int dmax = std::max({a.depth, a.depth, a.depth, a.depth});

				compressed.push_back({sum, dmax + 2});
				compressed.push_back({carry, dmax + 2});

				fa_count += 2;
				c42_count += 1;
				i += 4;
			} else if (remaining >= 3) {
				DepthSig a = ready[i + 0];
				DepthSig b = ready[i + 1];
				DepthSig c = ready[i + 2];

				auto [sum, carry] = emit_compressor_32(module, a.sig, b.sig, c.sig, width);
				int dmax = std::max({a.depth, b.depth, c.depth});

				compressed.push_back({sum, dmax + 1});
				compressed.push_back({carry, dmax + 1});

				fa_count += 1;
				i += 3;
			} else {
				// Uncompressed operands pass through to next level
				for (; i < ready.size(); i++)
					compressed.push_back(ready[i]);
				break;
			}
		}

		// Merge compressed with waiting operands
		for (auto &op : waiting)
			compressed.push_back(op);

		operands = std::move(compressed);
		levels++;
	}

	if(compressor_count)
		*compressor_count = fa_count;

	if (operands.size() == 0)
		return {SigSpec(State::S0, width), SigSpec(State::S0, width)};
	if (operands.size() == 1)
		return {operands[0].sig, SigSpec(State::S0, width)};

	final_depth = std::max(operands[0].depth, operands[1].depth);
	log_assert(operands.size() == 2);
	log("    CompressorTree::reduce_scheduled: %d levels, %d $fa (%d as 4:2), final depth %d\n", levels, fa_count, c42_count, final_depth);
	return {operands[0].sig, operands[1].sig};
}

/**
 * emit_kogge_stone() - Emit a Kogge-Stone parallel-prefix adder
 * @module: The Yosys module to which the gates will be added
 * @a: Signal A
 * @b: Signal B
 * @y: Signal Y = (A + B) mod 2^W
 */
inline void emit_kogge_stone(Module *module, SigSpec a, SigSpec b, SigSpec y)
{
	int width = GetSize(y);
	log_assert(GetSize(a) == width);
	log_assert(GetSize(b) == width);

	if (width == 0)
		return;

	if (width == 1) {
		module->addXorGate(NEW_ID, a[0], b[0], y[0]);
		return;
	}

	// Bit level gen and prop
	std::vector<SigBit> g_pre(width), p_pre(width);
	for (int i = 0; i < width; i++) {
		SigBit gi = module->addWire(NEW_ID);
		SigBit pi = module->addWire(NEW_ID);
		module->addAndGate(NEW_ID, a[i], b[i], gi);
		module->addXorGate(NEW_ID, a[i], b[i], pi);
		g_pre[i] = gi;
		p_pre[i] = pi;
	}

	// Propagate (g, p) through ceil(log2 W) levels
	std::vector<SigBit> g = g_pre;
	std::vector<SigBit> p = p_pre;
	int num_levels = 0;

	while ((1 << num_levels) < width)
		num_levels++;

	for (int k = 1; k <= num_levels; k++) {
		int s = 1 << (k - 1);
		std::vector<SigBit> g_next(width), p_next(width);
		for (int i = 0; i < width; i++) {
			if (i < s) {
				// Nothing to do
				g_next[i] = g[i];
				p_next[i] = p[i];
			} else {
				// g_i^k = g_i | (p_i & g_(i-s))
				SigBit and_pg = module->addWire(NEW_ID);
				module->addAndGate(NEW_ID, p[i], g[i - s], and_pg);
				SigBit gnew = module->addWire(NEW_ID);
				module->addOrGate(NEW_ID, g[i], and_pg, gnew);
				g_next[i] = gnew;

				// p_i^k = p_i & p_(i-s)
				if (k < num_levels) {
					SigBit pnew = module->addWire(NEW_ID);
					module->addAndGate(NEW_ID, p[i], p[i - s], pnew);
					p_next[i] = pnew;
				} else {
					// Skip last level
					p_next[i] = State::Sx;
				}
			}
		}

		g = std::move(g_next);
		p = std::move(p_next);
	}

	// Sum layer, g[i] is COUT of bit i
	// With CIN 0:
	//   sum[0] = p_pre[0]
	//   sum[i] = p_pre[i] ^ g[i-1] ...
	module->connect(y[0], p_pre[0]);
	for (int i = 1; i < width; i++)
		module->addXorGate(NEW_ID, p_pre[i], g[i - 1], y[i]);
}

/**
 * emit_final_adder() - Emit the final carry-propagate addition between the two reduced vectors
 * @module:The Yosys module to which the compressors will be added
 * @a: Signal A
 * @b: Signal B
 * @y: Signal Y
 * @choice: Adder type to instantiate
 * @any_signed: Signed info for library macros
 *
 * Return: Cell* of the emitted instance
 */
inline Cell *emit_final_adder(Module *module, SigSpec a, SigSpec b, SigSpec y, FinalAdder choice, bool any_signed) {
	switch (choice) {
		case FinalAdder::DEFAULT:
		case FinalAdder::RIPPLE: {
			return module->addAdd(NEW_ID, a, b, y, false);
		}
		case FinalAdder::PARALLEL_PREFIX: {
			emit_kogge_stone(module, a, b, y);
			return nullptr;
		}
		case FinalAdder::ELARITH_MOP_CSV: {
			Cell *c = module->addCell(NEW_ID, IdString("\\AddMopCsv"));
			int w = GetSize(y);
			c->setParam(IdString("\\WIDTH"), w);
			c->setParam(IdString("\\NUM_OPERANDS"), 2);
			c->setParam(IdString("\\SIGNED"), any_signed ? 1 : 0);
			c->setParam(IdString("\\SPEED"), Const("fast"));
			c->setPort(IdString("\\Operands"), {a, b});
			c->setPort(IdString("\\Sum"), y);
			return c;
		}
	}
	log_assert(false && "CompressorTree::emit_final_adder: invalid choice");
	return nullptr;
}

inline FinalAdder pick_final_adder(int width, FinalMode mode) {
	switch (mode) {
		case FinalMode::RIPPLE:  return FinalAdder::RIPPLE;
		case FinalMode::PREFIX:  return FinalAdder::PARALLEL_PREFIX;
		case FinalMode::ELARITH: return FinalAdder::ELARITH_MOP_CSV;
		case FinalMode::AUTO:
		default:                 return (width < RIPPLE_PREFIX_THRESHOLD) ? FinalAdder::DEFAULT : FinalAdder::PARALLEL_PREFIX;
	}
}

} // namespace CompressorTree

YOSYS_NAMESPACE_END

#endif // COMPRESSOR_TREE_H