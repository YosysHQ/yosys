/**
 * Generalized compressor-tree utilities for multi-operand addition
 *
 * Terminology:
 * - compressor: $fa viewed as reducing N inputs to M outputs (sum + shifted carry) (N:M compressor)
 * - level:      A stage of parallel compression operations
 * - depth:      Gate delays from any input to a signal. A compressor is not a fixed
 *               depth from each of its inputs (see fa_out_depth), so scheduling
 *               counts gates rather than levels.
 *
 * Supported compressors:
 * - 3:2 compressor
 * - 4:2 compressor
 *
 * References:
 * - "Some schemes for parallel multipliers" (https://www.acsel-lab.com/arithmetic/arith6/papers/ARITH6_Dadda.pdf)
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

// Width and depth thresholds below which a ripple is preferred over parallel-prefix
// NOTE: Based on "Binary Adder Architectures for Cell-Based VLSI and their Synthesis" (Tables 4.7, 4.9) - the threshold
//       should be the point where Kogge-Stone isn't strictly less efficient than RCA
constexpr int RIPPLE_PREFIX_WIDTH_THRESHOLD = 16;
// In gate delays, so about five compressor levels
constexpr int RIPPLE_PREFIX_DEPTH_THRESHOLD = 15;
// Gate delays a compressor level costs, i.e. the resolution a schedule can act on
constexpr int FA_GATE_DEPTH = 3;

enum class Strategy {
	FA_ONLY,   // 3:2 compressors
	PREFER_42, // Prefer 4:2 grouping when >=4 operands ready
	DADDA,     // Defer compression until column counts exceed
};

struct DepthSig {
	SigSpec sig;
	int depth; // gate delays
};

/**
 * fa_out_depth() - Gate delays to an $fa's outputs from its input depths
 *
 * fa_wordlevel lowers a full adder to t1 = A ^ B, sum = t1 ^ C and
 * carry = (A & B) | (C & t1), which is not symmetric in its inputs: C is two gates
 * from the carry and one from the sum, where A and B are three and two. Schedule a
 * group by putting its latest operand on C.
 *
 * Sum and carry are both charged the carry's depth. They enter the next level as a
 * pair, and letting the sum go a gate earlier only splits them across levels,
 * which costs more groupings than the gate is worth.
 */
inline int fa_out_depth(int da, int db, int dc)
{
	return std::max(std::max(da, db) + 3, dc + 2);
}

enum class FinalAdder {
	DEFAULT,         // emit $add and let downstream techmap pick
	RIPPLE,          // emit $add with explicit narrow hint
	PARALLEL_PREFIX, // emit $add with PARALLEL_PREFIX
};

enum class FinalMode {
	AUTO,
	RIPPLE,
	PREFIX,
};

// SILIMATE: every emitter takes cell_name, the originating cell, so the emitted
// logic inherits a readable name instead of an $auto$file.cc:line$id one
std::pair<SigSpec, SigSpec> emit_compressor_32(Module *module, SigSpec a, SigSpec b, SigSpec c, int width, IdString cell_name);
std::pair<SigSpec, SigSpec> emit_compressor_42(Module *module, SigSpec a, SigSpec b, SigSpec c, SigSpec d, int width, IdString cell_name);

/**
 * generate_partial_products() - Generate partial products for FMA concat
 * @module:The Yosys module to which the compressors will be added
 * @a: Signal A
 * @b: Signal B
 * @a_signed: Whether signal A is signed
 * @b_signed: Whether signal B is signed
 * @width: Target width
 * @cell_name: Originating cell, used to name the emitted logic
 *
 * Return: Partial-product matrix as a set of depth-0 vectors
 */
std::vector<DepthSig> generate_partial_products(Module *module, SigSpec a, SigSpec b, bool a_signed, bool b_signed, int width, IdString cell_name);

/**
 * reduce_scheduled() - Reduce multiple operands to two using a compressor tree
 * @module: The Yosys module to which the compressors will be added
 * @operands: Vector of operands to be reduced
 * @sigs: Vector of input signals (operands) to be reduced
 * @width: Target bit-width to which all operands will be zero-extended
 * @strategy: Compression strategy to use
 * @cell_name: Originating cell, used to name the emitted logic
 * @out_compressor_count: Optional pointer to return the number of $fa cells emitted
 * @out_final_depth: Optional pointer to return the final depth of the scheduled tree
 *
 * Return: The final two reduced operands, that are to be fed into an adder
 */
std::pair<SigSpec, SigSpec> reduce_scheduled(Module *module, std::vector<DepthSig> operands, int width, Strategy strategy, IdString cell_name, int *out_compressor_count = nullptr, int *out_final_depth = nullptr);

/**
 * emit_kogge_stone() - Emit a Kogge-Stone parallel-prefix adder
 * @module: The Yosys module to which the gates will be added
 * @a: Signal A
 * @b: Signal B
 * @y: Signal Y = (A + B) mod 2^W
 * @cell_name: Originating cell, used to name the emitted logic
 */
void emit_kogge_stone(Module *module, SigSpec a, SigSpec b, SigSpec y, IdString cell_name);

/**
 * emit_final_adder() - Emit the final carry-propagate addition between the two reduced vectors
 * @module:The Yosys module to which the compressors will be added
 * @a: Signal A
 * @b: Signal B
 * @y: Signal Y
 * @choice: Adder type to instantiate
 * @cell_name: Originating cell, used to name the emitted logic
 *
 * Return: Cell* of the emitted instance
 */
Cell *emit_final_adder(Module *module, SigSpec a, SigSpec b, SigSpec y, FinalAdder choice, IdString cell_name);

FinalAdder pick_final_adder(int width, int final_depth, FinalMode mode);

} // namespace CompressorTree

YOSYS_NAMESPACE_END

#endif // COMPRESSOR_TREE_H
