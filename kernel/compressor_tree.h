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
constexpr int RIPPLE_PREFIX_DEPTH_THRESHOLD = 5;

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
};

enum class FinalMode {
	AUTO,
	RIPPLE,
	PREFIX,
};

std::pair<SigSpec, SigSpec> emit_compressor_32(Module *module, SigSpec a, SigSpec b, SigSpec c, int width);
std::pair<SigSpec, SigSpec> emit_compressor_42(Module *module, SigSpec a, SigSpec b, SigSpec c, SigSpec d, int width);

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
std::vector<DepthSig> generate_partial_products(Module *module, SigSpec a, SigSpec b, bool a_signed, bool b_signed, int width);

/**
 * reduce_scheduled() - Reduce multiple operands to two using a compressor tree
 * @module: The Yosys module to which the compressors will be added
 * @operands: Vector of operands to be reduced
 * @sigs: Vector of input signals (operands) to be reduced
 * @width: Target bit-width to which all operands will be zero-extended
 * @strategy: Compression strategy to use
 * @out_compressor_count: Optional pointer to return the number of $fa cells emitted
 * @out_final_depth: Optional pointer to return the final depth of the scheduled tree
 *
 * Return: The final two reduced operands, that are to be fed into an adder
 */
std::pair<SigSpec, SigSpec> reduce_scheduled(Module *module, std::vector<DepthSig> operands, int width, Strategy strategy, int *out_compressor_count = nullptr, int *out_final_depth = nullptr);

/**
 * emit_kogge_stone() - Emit a Kogge-Stone parallel-prefix adder
 * @module: The Yosys module to which the gates will be added
 * @a: Signal A
 * @b: Signal B
 * @y: Signal Y = (A + B) mod 2^W
 */
void emit_kogge_stone(Module *module, SigSpec a, SigSpec b, SigSpec y);

/**
 * emit_final_adder() - Emit the final carry-propagate addition between the two reduced vectors
 * @module:The Yosys module to which the compressors will be added
 * @a: Signal A
 * @b: Signal B
 * @y: Signal Y
 * @choice: Adder type to instantiate
 *
 * Return: Cell* of the emitted instance
 */
Cell *emit_final_adder(Module *module, SigSpec a, SigSpec b, SigSpec y, FinalAdder choice);

FinalAdder pick_final_adder(int width, int final_depth, FinalMode mode);

} // namespace CompressorTree

YOSYS_NAMESPACE_END

#endif // COMPRESSOR_TREE_H
