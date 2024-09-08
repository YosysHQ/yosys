/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2024  Emily Schmidt <emily@yosyshq.com>
 *  Copyright (C) 2024 National Technology and Engineering Solutions of Sandia, LLC
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */

#include "kernel/functional.h"
#include "kernel/topo_scc.h"
#include "ff.h"
#include "ffinit.h"
#include <deque>

YOSYS_NAMESPACE_BEGIN
namespace Functional {

const char *fn_to_string(Fn fn) {
	switch(fn) {
	case Fn::invalid: return "invalid";
	case Fn::buf: return "buf";
	case Fn::slice: return "slice";
	case Fn::zero_extend: return "zero_extend";
	case Fn::sign_extend: return "sign_extend";
	case Fn::concat: return "concat";
	case Fn::add: return "add";
	case Fn::sub: return "sub";
	case Fn::mul: return "mul";
	case Fn::unsigned_div: return "unsigned_div";
	case Fn::unsigned_mod: return "unsigned_mod";
	case Fn::bitwise_and: return "bitwise_and";
	case Fn::bitwise_or: return "bitwise_or";
	case Fn::bitwise_xor: return "bitwise_xor";
	case Fn::bitwise_not: return "bitwise_not";
	case Fn::reduce_and: return "reduce_and";
	case Fn::reduce_or: return "reduce_or";
	case Fn::reduce_xor: return "reduce_xor";
	case Fn::unary_minus: return "unary_minus";
	case Fn::equal: return "equal";
	case Fn::not_equal: return "not_equal";
	case Fn::signed_greater_than: return "signed_greater_than";
	case Fn::signed_greater_equal: return "signed_greater_equal";
	case Fn::unsigned_greater_than: return "unsigned_greater_than";
	case Fn::unsigned_greater_equal: return "unsigned_greater_equal";
	case Fn::logical_shift_left: return "logical_shift_left";
	case Fn::logical_shift_right: return "logical_shift_right";
	case Fn::arithmetic_shift_right: return "arithmetic_shift_right";
	case Fn::mux: return "mux";
	case Fn::constant: return "constant";
	case Fn::input: return "input";
	case Fn::state: return "state";
	case Fn::memory_read: return "memory_read";
	case Fn::memory_write: return "memory_write";
	}
	log_error("fn_to_string: unknown Functional::Fn value %d", (int)fn);
}

vector<IRInput const*> IR::inputs(IdString kind) const {
	vector<IRInput const*> ret;
	for (const auto &[name, input] : _inputs)
		if(input.kind == kind)
			ret.push_back(&input);
	return ret;
}

vector<IROutput const*> IR::outputs(IdString kind) const {
	vector<IROutput const*> ret;
	for (const auto &[name, output] : _outputs)
		if(output.kind == kind)
			ret.push_back(&output);
	return ret;
}

vector<IRState const*> IR::states(IdString kind) const {
	vector<IRState const*> ret;
	for (const auto &[name, state] : _states)
		if(state.kind == kind)
			ret.push_back(&state);
	return ret;
}

vector<IRInput const*> IR::all_inputs() const {
	vector<IRInput const*> ret;
	for (const auto &[name, input] : _inputs)
		ret.push_back(&input);
	return ret;
}

vector<IROutput const*> IR::all_outputs() const {
	vector<IROutput const*> ret;
	for (const auto &[name, output] : _outputs)
		ret.push_back(&output);
	return ret;
}

vector<IRState const*> IR::all_states() const {
	vector<IRState const*> ret;
	for (const auto &[name, state] : _states)
		ret.push_back(&state);
	return ret;
}

struct PrintVisitor : DefaultVisitor<std::string> {
	std::function<std::string(Node)> np;
	PrintVisitor(std::function<std::string(Node)> np) : np(np) { }
	// as a general rule the default handler is good enough iff the only arguments are of type Node
	std::string slice(Node, Node a, int offset, int out_width) override { return "slice(" + np(a) + ", " + std::to_string(offset) + ", " + std::to_string(out_width) + ")"; }
	std::string zero_extend(Node, Node a, int out_width) override { return "zero_extend(" + np(a) + ", " + std::to_string(out_width) + ")"; }
	std::string sign_extend(Node, Node a, int out_width) override { return "sign_extend(" + np(a) + ", " + std::to_string(out_width) + ")"; }
	std::string constant(Node, RTLIL::Const const& value) override { return "constant(" + value.as_string() + ")"; }
	std::string input(Node, IdString name, IdString kind) override { return "input(" + name.str() + ", " + kind.str() + ")"; }
	std::string state(Node, IdString name, IdString kind) override { return "state(" + name.str() + ", " + kind.str() + ")"; }
	std::string default_handler(Node self) override {
		std::string ret = fn_to_string(self.fn());
		ret += "(";
		for(size_t i = 0; i < self.arg_count(); i++) {
			if(i > 0) ret += ", ";
			ret += np(self.arg(i));
		}
		ret += ")";
		return ret;
	}
};

std::string Node::to_string()
{
	return to_string([](Node n) { return RTLIL::unescape_id(n.name()); });
}

std::string Node::to_string(std::function<std::string(Node)> np)
{
	return visit(PrintVisitor(np));
}

class CellSimplifier {
	Factory &factory;
	Node sign(Node a) {
		return factory.slice(a, a.width() - 1, 1);
	}
	Node neg_if(Node a, Node s) {
		return factory.mux(a, factory.unary_minus(a), s);
	}
	Node abs(Node a) {
		return neg_if(a, sign(a));
	}
	Node handle_shift(Node a, Node b, bool is_right, bool is_signed) {
		// to prevent new_width == 0, we handle this case separately
		if(a.width() == 1) {
			if(!is_signed)
				return factory.bitwise_and(a, factory.bitwise_not(factory.reduce_or(b)));
			else
				return a;
		}
		int new_width = ceil_log2(a.width());
		Node b_truncated = factory.extend(b, new_width, false);
		Node y =
			!is_right ? factory.logical_shift_left(a, b_truncated) :
			!is_signed ? factory.logical_shift_right(a, b_truncated) :
			factory.arithmetic_shift_right(a, b_truncated);
		if(b.width() <= new_width)
			return y;
		Node overflow = factory.unsigned_greater_equal(b, factory.constant(RTLIL::Const(a.width(), b.width())));
		Node y_if_overflow = is_signed ? factory.extend(sign(a), a.width(), true) : factory.constant(RTLIL::Const(State::S0, a.width()));
		return factory.mux(y, y_if_overflow, overflow);
	}
public:
	Node logical_shift_left(Node a, Node b) { return handle_shift(a, b, false, false); }
	Node logical_shift_right(Node a, Node b) { return handle_shift(a, b, true, false); }
	Node arithmetic_shift_right(Node a, Node b) { return handle_shift(a, b, true, true); }
	Node bitwise_mux(Node a, Node b, Node s) {
		Node aa = factory.bitwise_and(a, factory.bitwise_not(s));
		Node bb = factory.bitwise_and(b, s);
		return factory.bitwise_or(aa, bb);
	}
	CellSimplifier(Factory &f) : factory(f) {}
private:
	Node handle_pow(Node a0, Node b, int y_width, bool is_signed) {
		Node a = factory.extend(a0, y_width, is_signed);
		Node r = factory.constant(Const(1, y_width));
		for(int i = 0; i < b.width(); i++) {
			Node b_bit = factory.slice(b, i, 1);
			r = factory.mux(r, factory.mul(r, a), b_bit);
			a = factory.mul(a, a);
		}
		if (is_signed) {
			Node a_ge_1 = factory.unsigned_greater_than(abs(a0), factory.constant(Const(1, a0.width())));
			Node zero_result = factory.bitwise_and(a_ge_1, sign(b));
			r = factory.mux(r, factory.constant(Const(0, y_width)), zero_result);
		}
		return r;
	}
	Node handle_bmux(Node a, Node s, int a_offset, int width, int sn) {
		if(sn < 1)
			return factory.slice(a, a_offset, width);
		else {
			Node y0 = handle_bmux(a, s, a_offset, width, sn - 1);
			Node y1 = handle_bmux(a, s, a_offset + (width << (sn - 1)), width, sn - 1);
			return factory.mux(y0, y1, factory.slice(s, sn - 1, 1));
		}
	}
	Node handle_pmux(Node a, Node b, Node s) {
		// TODO : what to do about multiple b bits set ?
		log_assert(b.width() == a.width() * s.width());
		Node y = a;
		for(int i = 0; i < s.width(); i++)
			y = factory.mux(y, factory.slice(b, a.width() * i, a.width()), factory.slice(s, i, 1));
		return y;
	}
	dict<IdString, Node> handle_fa(Node a, Node b, Node c) {
		Node t1 = factory.bitwise_xor(a, b);
		Node t2 = factory.bitwise_and(a, b);
		Node t3 = factory.bitwise_and(c, t1);
		Node y = factory.bitwise_xor(c, t1);
		Node x = factory.bitwise_or(t2, t3);
		return {{ID(X), x}, {ID(Y), y}};
	}
	dict<IdString, Node> handle_alu(Node a_in, Node b_in, int y_width, bool is_signed, Node ci, Node bi) {
		Node a = factory.extend(a_in, y_width, is_signed);
		Node b_uninverted = factory.extend(b_in, y_width, is_signed);
		Node b = factory.mux(b_uninverted, factory.bitwise_not(b_uninverted), bi);
		Node x = factory.bitwise_xor(a, b);
		// we can compute the carry into each bit using (a+b+c)^a^b. since we want the carry out,
		// i.e. the carry into the next bit, we have to add an extra bit to a and b, and
		// then slice off the bottom bit of the result.
		Node a_extra = factory.extend(a, y_width + 1, false);
		Node b_extra = factory.extend(b, y_width + 1, false);
		Node y_extra = factory.add(factory.add(a_extra, b_extra), factory.extend(ci, a.width() + 1, false));
		Node y = factory.slice(y_extra, 0, y_width);
		Node carries = factory.bitwise_xor(y_extra, factory.bitwise_xor(a_extra, b_extra));
		Node co = factory.slice(carries, 1, y_width);
		return {{ID(X), x}, {ID(Y), y}, {ID(CO), co}};
	}
	Node handle_lcu(Node p, Node g, Node ci) {
		return handle_alu(g, factory.bitwise_or(p, g), g.width(), false, ci, factory.constant(Const(State::S0, 1))).at(ID(CO));
	}
public:
	std::variant<dict<IdString, Node>, Node> handle(IdString cellName, IdString cellType, dict<IdString, Const> parameters, dict<IdString, Node> inputs)
	{
		int a_width = parameters.at(ID(A_WIDTH), Const(-1)).as_int();
		int b_width = parameters.at(ID(B_WIDTH), Const(-1)).as_int();
		int y_width = parameters.at(ID(Y_WIDTH), Const(-1)).as_int();
		bool a_signed = parameters.at(ID(A_SIGNED), Const(0)).as_bool();
		bool b_signed = parameters.at(ID(B_SIGNED), Const(0)).as_bool();
		if(cellType.in({ID($add), ID($sub), ID($and), ID($or), ID($xor), ID($xnor), ID($mul)})){
			bool is_signed = a_signed && b_signed;
			Node a = factory.extend(inputs.at(ID(A)), y_width, is_signed);
			Node b = factory.extend(inputs.at(ID(B)), y_width, is_signed);
			if(cellType == ID($add))
				return factory.add(a, b);
			else if(cellType == ID($sub))
				return factory.sub(a, b);
			else if(cellType == ID($mul))
				return factory.mul(a, b);
			else if(cellType == ID($and))
				return factory.bitwise_and(a, b);
			else if(cellType == ID($or))
				return factory.bitwise_or(a, b);
			else if(cellType == ID($xor))
				return factory.bitwise_xor(a, b);
			else if(cellType == ID($xnor))
				return factory.bitwise_not(factory.bitwise_xor(a, b));
			else
				log_abort();
		}else if(cellType.in({ID($eq), ID($ne), ID($eqx), ID($nex), ID($le), ID($lt), ID($ge), ID($gt)})){
			bool is_signed = a_signed && b_signed;
			int width = max(a_width, b_width);
			Node a = factory.extend(inputs.at(ID(A)), width, is_signed);
			Node b = factory.extend(inputs.at(ID(B)), width, is_signed);
			if(cellType.in({ID($eq), ID($eqx)}))
				return factory.extend(factory.equal(a, b), y_width, false);
			else if(cellType.in({ID($ne), ID($nex)}))
				return factory.extend(factory.not_equal(a, b), y_width, false);
			else if(cellType == ID($lt))
				return factory.extend(is_signed ? factory.signed_greater_than(b, a) : factory.unsigned_greater_than(b, a), y_width, false);
			else if(cellType == ID($le))
				return factory.extend(is_signed ? factory.signed_greater_equal(b, a) : factory.unsigned_greater_equal(b, a), y_width, false);
			else if(cellType == ID($gt))
				return factory.extend(is_signed ? factory.signed_greater_than(a, b) : factory.unsigned_greater_than(a, b), y_width, false);
			else if(cellType == ID($ge))
				return factory.extend(is_signed ? factory.signed_greater_equal(a, b) : factory.unsigned_greater_equal(a, b), y_width, false);
			else
				log_abort();
		}else if(cellType.in({ID($logic_or), ID($logic_and)})){
			Node a = factory.reduce_or(inputs.at(ID(A)));
			Node b = factory.reduce_or(inputs.at(ID(B)));
			Node y = cellType == ID($logic_and) ? factory.bitwise_and(a, b) : factory.bitwise_or(a, b);
			return factory.extend(y, y_width, false);
		}else if(cellType == ID($not)){
			Node a = factory.extend(inputs.at(ID(A)), y_width, a_signed);
			return factory.bitwise_not(a);
		}else if(cellType == ID($pos)){
			return factory.extend(inputs.at(ID(A)), y_width, a_signed);
		}else if(cellType == ID($neg)){
			Node a = factory.extend(inputs.at(ID(A)), y_width, a_signed);
			return factory.unary_minus(a);
		}else if(cellType == ID($logic_not)){
			Node a = factory.reduce_or(inputs.at(ID(A)));
			Node y = factory.bitwise_not(a);
			return factory.extend(y, y_width, false);
		}else if(cellType.in({ID($reduce_or), ID($reduce_bool)})){
			Node a = factory.reduce_or(inputs.at(ID(A)));
			return factory.extend(a, y_width, false);
		}else if(cellType == ID($reduce_and)){
			Node a = factory.reduce_and(inputs.at(ID(A)));
			return factory.extend(a, y_width, false);
		}else if(cellType.in({ID($reduce_xor), ID($reduce_xnor)})){
			Node a = factory.reduce_xor(inputs.at(ID(A)));
			Node y = cellType == ID($reduce_xnor) ? factory.bitwise_not(a) : a;
			return factory.extend(y, y_width, false);
		}else if(cellType == ID($shl) || cellType == ID($sshl)){
			Node a = factory.extend(inputs.at(ID(A)), y_width, a_signed);
			Node b = inputs.at(ID(B));
			return logical_shift_left(a, b);
		}else if(cellType == ID($shr) || cellType == ID($sshr)){
			int width = max(a_width, y_width);
			Node a = factory.extend(inputs.at(ID(A)), width, a_signed);
			Node b = inputs.at(ID(B));
			Node y = a_signed && cellType == ID($sshr) ?
				arithmetic_shift_right(a, b) :
				logical_shift_right(a, b);
			return factory.extend(y, y_width, a_signed);
		}else if(cellType == ID($shiftx) || cellType == ID($shift)){
			int width = max(a_width, y_width);
			Node a = factory.extend(inputs.at(ID(A)), width, cellType == ID($shift) && a_signed);
			Node b = inputs.at(ID(B));
			Node shr = logical_shift_right(a, b);
			if(b_signed) {
				Node shl = logical_shift_left(a, factory.unary_minus(b));
				Node y = factory.mux(shr, shl, sign(b));
				return factory.extend(y, y_width, false);
			} else {
				return factory.extend(shr, y_width, false);
			}
		}else if(cellType == ID($mux)){
			return factory.mux(inputs.at(ID(A)), inputs.at(ID(B)), inputs.at(ID(S)));
		}else if(cellType == ID($pmux)){
			return handle_pmux(inputs.at(ID(A)), inputs.at(ID(B)), inputs.at(ID(S)));
		}else if(cellType == ID($concat)){
			Node a = inputs.at(ID(A));
			Node b = inputs.at(ID(B));
			return factory.concat(a, b);
		}else if(cellType == ID($slice)){
			int offset = parameters.at(ID(OFFSET)).as_int();
			Node a = inputs.at(ID(A));
			return factory.slice(a, offset, y_width);
		}else if(cellType.in({ID($div), ID($mod), ID($divfloor), ID($modfloor)})) {
			int width = max(a_width, b_width);
			bool is_signed = a_signed && b_signed;
			Node a = factory.extend(inputs.at(ID(A)), width, is_signed);
			Node b = factory.extend(inputs.at(ID(B)), width, is_signed);
			if(is_signed) {
				if(cellType == ID($div)) {
					// divide absolute values, then flip the sign if input signs differ
					// but extend the width first, to handle the case (most negative value) / (-1)
					Node abs_y = factory.unsigned_div(abs(a), abs(b));
					Node out_sign = factory.not_equal(sign(a), sign(b));
					return neg_if(factory.extend(abs_y, y_width, false), out_sign);
				} else if(cellType == ID($mod)) {
					// similar to division but output sign == divisor sign
					Node abs_y = factory.unsigned_mod(abs(a), abs(b));
					return neg_if(factory.extend(abs_y, y_width, false), sign(a));
				} else if(cellType == ID($divfloor)) {
					// if b is negative, flip both signs so that b is positive
					Node b_sign = sign(b);
					Node a1 = neg_if(a, b_sign);
					Node b1 = neg_if(b, b_sign);
					// if a is now negative, calculate ~((~a) / b) = -((-a - 1) / b + 1)
					// which equals the negative of (-a) / b with rounding up rather than down
					// note that to handle the case where a = most negative value properly,
					// we have to calculate a1_sign from the original values rather than using sign(a1)
					Node a1_sign = factory.bitwise_and(factory.not_equal(sign(a), sign(b)), factory.reduce_or(a));
					Node a2 = factory.mux(a1, factory.bitwise_not(a1), a1_sign);
					Node y1 = factory.unsigned_div(a2, b1);
					Node y2 = factory.extend(y1, y_width, false);
					return factory.mux(y2, factory.bitwise_not(y2), a1_sign);
				} else if(cellType == ID($modfloor)) {
					// calculate |a| % |b| and then subtract from |b| if input signs differ and the remainder is non-zero
					Node abs_b = abs(b);
					Node abs_y = factory.unsigned_mod(abs(a), abs_b);
					Node flip_y = factory.bitwise_and(factory.bitwise_xor(sign(a), sign(b)), factory.reduce_or(abs_y));
					Node y_flipped = factory.mux(abs_y, factory.sub(abs_b, abs_y), flip_y);
					// since y_flipped is strictly less than |b|, the top bit is always 0 and we can just sign extend the flipped result
					Node y = neg_if(y_flipped, sign(b));
					return factory.extend(y, y_width, true);
				} else
					log_error("unhandled cell in CellSimplifier %s\n", cellType.c_str());
			} else {
				if(cellType.in({ID($mod), ID($modfloor)}))
					return factory.extend(factory.unsigned_mod(a, b), y_width, false);
				else
					return factory.extend(factory.unsigned_div(a, b), y_width, false);
			}
		} else if(cellType == ID($pow)) {
			return handle_pow(inputs.at(ID(A)), inputs.at(ID(B)), y_width, a_signed && b_signed);
		} else if (cellType == ID($lut)) {
			int width = parameters.at(ID(WIDTH)).as_int();
			Const lut_table = parameters.at(ID(LUT));
			lut_table.extu(1 << width);
			return handle_bmux(factory.constant(lut_table), inputs.at(ID(A)), 0, 1, width);
		} else if (cellType == ID($bwmux)) {
			Node a = inputs.at(ID(A));
			Node b = inputs.at(ID(B));
			Node s = inputs.at(ID(S));
			return factory.bitwise_or(
				factory.bitwise_and(a, factory.bitwise_not(s)),
				factory.bitwise_and(b, s));
		} else if (cellType == ID($bweqx)) {
			Node a = inputs.at(ID(A));
			Node b = inputs.at(ID(B));
			return factory.bitwise_not(factory.bitwise_xor(a, b));
		} else if(cellType == ID($bmux)) {
			int width = parameters.at(ID(WIDTH)).as_int();
			int s_width = parameters.at(ID(S_WIDTH)).as_int();
			return handle_bmux(inputs.at(ID(A)), inputs.at(ID(S)), 0, width, s_width);
		} else if(cellType == ID($demux)) {
			int width = parameters.at(ID(WIDTH)).as_int();
			int s_width = parameters.at(ID(S_WIDTH)).as_int();
			int y_width = width << s_width;
			int b_width = ceil_log2(y_width);
			Node a = factory.extend(inputs.at(ID(A)), y_width, false);
			Node s = factory.extend(inputs.at(ID(S)), b_width, false);
			Node b = factory.mul(s, factory.constant(Const(width, b_width)));
			return factory.logical_shift_left(a, b);
		} else if(cellType == ID($fa)) {
			return handle_fa(inputs.at(ID(A)), inputs.at(ID(B)), inputs.at(ID(C)));
		} else if(cellType == ID($lcu)) {
			return handle_lcu(inputs.at(ID(P)), inputs.at(ID(G)), inputs.at(ID(CI)));
		} else if(cellType == ID($alu)) {
			return handle_alu(inputs.at(ID(A)), inputs.at(ID(B)), y_width, a_signed && b_signed, inputs.at(ID(CI)), inputs.at(ID(BI)));
		} else if(cellType.in({ID($assert), ID($assume), ID($live), ID($fair), ID($cover)})) {
			Node a = factory.mux(factory.constant(Const(State::S1, 1)), inputs.at(ID(A)), inputs.at(ID(EN)));
			auto &output = factory.add_output(cellName, cellType, Sort(1));
			output.set_value(a);
			return {};
		} else if(cellType.in({ID($anyconst), ID($allconst), ID($anyseq), ID($allseq)})) {
			int width = parameters.at(ID(WIDTH)).as_int();
			auto &input = factory.add_input(cellName, cellType, Sort(width));
			return factory.value(input);
		} else if(cellType == ID($initstate)) {
			if(factory.ir().has_state(ID($initstate), ID($state)))
				return factory.value(factory.ir().state(ID($initstate)));
			else {
				auto &state = factory.add_state(ID($initstate), ID($state), Sort(1));
				state.set_initial_value(RTLIL::Const(State::S1, 1));
				state.set_next_value(factory.constant(RTLIL::Const(State::S0, 1)));
				return factory.value(state);
			}
		} else if(cellType == ID($check)) {
			log_error("The design contains a $check cell `%s'. This is not supported by the functional backend. Call `chformal -lower' to avoid this error.\n", cellName.c_str());
		} else {
			log_error("`%s' cells are not supported by the functional backend\n", cellType.c_str());
		}
	}
};

class FunctionalIRConstruction {
	std::deque<std::variant<DriveSpec, Cell *>> queue;
	dict<DriveSpec, Node> graph_nodes;
	dict<std::pair<Cell *, IdString>, Node> cell_outputs;
	DriverMap driver_map;
	Factory& factory;
	CellSimplifier simplifier;
	vector<Mem> memories_vector;
	dict<Cell*, Mem*> memories;
	SigMap sig_map; // TODO: this is only for FfInitVals, remove this once FfInitVals supports DriverMap
	FfInitVals ff_initvals;

	Node enqueue(DriveSpec const &spec)
	{
		auto it = graph_nodes.find(spec);
		if(it == graph_nodes.end()){
			auto node = factory.create_pending(spec.size());
			graph_nodes.insert({spec, node});
			queue.emplace_back(spec);
			return node;
		}else
			return it->second;
	}
	Node enqueue_cell(Cell *cell, IdString port_name)
	{
		auto it = cell_outputs.find({cell, port_name});
		if(it == cell_outputs.end()) {
			queue.emplace_back(cell);
			std::optional<Node> rv;
			for(auto const &[name, sigspec] : cell->connections())
				if(driver_map.celltypes.cell_output(cell->type, name)) {
					auto node = factory.create_pending(sigspec.size());
					factory.suggest_name(node, cell->name.str() + "$" + name.str());
					cell_outputs.emplace({cell, name}, node);
					if(name == port_name)
						rv = node;
				}
			return *rv;
		} else
			return it->second;
	}
public:
	FunctionalIRConstruction(Module *module, Factory &f)
		: factory(f)
		, simplifier(f)
		, sig_map(module)
		, ff_initvals(&sig_map, module)
	{
		driver_map.add(module);
		for (auto cell : module->cells()) {
			if (cell->type.in(ID($assert), ID($assume), ID($live), ID($fair), ID($cover), ID($check)))
				queue.emplace_back(cell);
		}
		for (auto wire : module->wires()) {
			if (wire->port_input)
				factory.add_input(wire->name, ID($input), Sort(wire->width));
			if (wire->port_output) {
				auto &output = factory.add_output(wire->name, ID($output), Sort(wire->width));
				output.set_value(enqueue(DriveChunk(DriveChunkWire(wire, 0, wire->width))));
			}
		}
		memories_vector = Mem::get_all_memories(module);
		for (auto &mem : memories_vector) {
			if (mem.cell != nullptr)
				memories[mem.cell] = &mem;
		}
	}
private:
	Node concatenate_read_results(Mem *mem, vector<Node> results)
	{
		// sanity check: all read ports concatenated should equal to the RD_DATA port
		const SigSpec &rd_data = mem->cell->connections().at(ID(RD_DATA));
		int current = 0;
		for(size_t i = 0; i < mem->rd_ports.size(); i++) {
			int width = mem->width << mem->rd_ports[i].wide_log2;
			log_assert (results[i].width() == width);
			log_assert (mem->rd_ports[i].data == rd_data.extract(current, width));
			current += width;
		}
		log_assert (current == rd_data.size());
		log_assert (!results.empty());
		Node node = results[0];
		for(size_t i = 1; i < results.size(); i++)
			node = factory.concat(node, results[i]);
		return node;
	}
	Node handle_memory(Mem *mem)
	{
		// To simplify memory handling, the functional backend makes the following assumptions:
		// - Since async2sync or clk2fflogic must be run to use the functional backend,
		//   we can assume that all ports are asynchronous.
		// - Async rd/wr are always transparent and so we must do reads after writes,
		//   but we can ignore transparency_mask.
		// - We ignore collision_x_mask because x is a dont care value for us anyway.
		// - Since wr port j can only have priority over wr port i if j > i, if we do writes in
		//   ascending index order the result will obey the priorty relation.
		vector<Node> read_results;
		auto &state = factory.add_state(mem->cell->name, ID($state), Sort(ceil_log2(mem->size), mem->width));
		state.set_initial_value(MemContents(mem));
		Node node = factory.value(state);
		for (size_t i = 0; i < mem->wr_ports.size(); i++) {
			const auto &wr = mem->wr_ports[i];
			if (wr.clk_enable)
				log_error("Write port %zd of memory %s.%s is clocked. This is not supported by the functional backend. "
					"Call async2sync or clk2fflogic to avoid this error.\n", i, log_id(mem->module), log_id(mem->memid));
			Node en = enqueue(driver_map(DriveSpec(wr.en)));
			Node addr = enqueue(driver_map(DriveSpec(wr.addr)));
			Node new_data = enqueue(driver_map(DriveSpec(wr.data)));
			Node old_data = factory.memory_read(node, addr);
			Node wr_data = simplifier.bitwise_mux(old_data, new_data, en);
			node = factory.memory_write(node, addr, wr_data);
		}
		if (mem->rd_ports.empty())
			log_error("Memory %s.%s has no read ports. This is not supported by the functional backend. "
				"Call opt_clean to remove it.", log_id(mem->module), log_id(mem->memid));
		for (size_t i = 0; i < mem->rd_ports.size(); i++) {
			const auto &rd = mem->rd_ports[i];
			if (rd.clk_enable)
				log_error("Read port %zd of memory %s.%s is clocked. This is not supported by the functional backend. "
					"Call memory_nordff to avoid this error.\n", i, log_id(mem->module), log_id(mem->memid));
			Node addr = enqueue(driver_map(DriveSpec(rd.addr)));
			read_results.push_back(factory.memory_read(node, addr));
		}
		state.set_next_value(node);
		return concatenate_read_results(mem, read_results);
	}
	void process_cell(Cell *cell)
	{
		if (cell->is_mem_cell()) {
			Mem *mem = memories.at(cell, nullptr);
			if (mem == nullptr) {
				log_assert(cell->has_memid());
				log_error("The design contains an unpacked memory at %s. This is not supported by the functional backend. "
					"Call memory_collect to avoid this error.\n", log_const(cell->parameters.at(ID(MEMID))));
			}
			Node node = handle_memory(mem);
			factory.update_pending(cell_outputs.at({cell, ID(RD_DATA)}), node);
		} else if (RTLIL::builtin_ff_cell_types().count(cell->type)) {
			FfData ff(&ff_initvals, cell);
			if (!ff.has_gclk)
				log_error("The design contains a %s flip-flop at %s. This is not supported by the functional backend. "
					"Call async2sync or clk2fflogic to avoid this error.\n", log_id(cell->type), log_id(cell));
			auto &state = factory.add_state(ff.name, ID($state), Sort(ff.width));
			Node q_value = factory.value(state);
			factory.suggest_name(q_value, ff.name);
			factory.update_pending(cell_outputs.at({cell, ID(Q)}), q_value);
			state.set_next_value(enqueue(ff.sig_d));
			state.set_initial_value(ff.val_init);
		} else {
			dict<IdString, Node> connections;
			IdString output_name; // for the single output case
			int n_outputs = 0;
			for(auto const &[name, sigspec] : cell->connections()) {
				if(driver_map.celltypes.cell_input(cell->type, name) && sigspec.size() > 0)
					connections.insert({ name, enqueue(DriveChunkPort(cell, {name, sigspec})) });
				if(driver_map.celltypes.cell_output(cell->type, name)) {
					output_name = name;
					n_outputs++;
				}
			}
			std::variant<dict<IdString, Node>, Node> outputs = simplifier.handle(cell->name, cell->type, cell->parameters, connections);
			if(auto *nodep = std::get_if<Node>(&outputs); nodep != nullptr) {
				log_assert(n_outputs == 1);
				factory.update_pending(cell_outputs.at({cell, output_name}), *nodep);
			} else {
				for(auto [name, node] : std::get<dict<IdString, Node>>(outputs))
					factory.update_pending(cell_outputs.at({cell, name}), node);
			}
		}
	}
	void undriven(const char *name) {
		log_error("The design contains an undriven signal %s. This is not supported by the functional backend. "
			"Call setundef with appropriate options to avoid this error.\n", name);
	}
	// we perform this check separately to give better error messages that include the wire or port name
	void check_undriven(DriveSpec const& spec, std::string const& name) {
		for(auto const &chunk : spec.chunks())
			if(chunk.is_none())
				undriven(name.c_str());
	}
public:
	void process_queue()
	{
		for (; !queue.empty(); queue.pop_front()) {
			if(auto p = std::get_if<Cell *>(&queue.front()); p != nullptr) {
				process_cell(*p);
				continue;
			}

			DriveSpec spec = std::get<DriveSpec>(queue.front());
			Node pending = graph_nodes.at(spec);

			if (spec.chunks().size() > 1) {
				auto chunks = spec.chunks();
				Node node = enqueue(chunks[0]);
				for(size_t i = 1; i < chunks.size(); i++)
					node = factory.concat(node, enqueue(chunks[i]));
				factory.update_pending(pending, node);
			} else if (spec.chunks().size() == 1) {
				DriveChunk chunk = spec.chunks()[0];
				if (chunk.is_wire()) {
					DriveChunkWire wire_chunk = chunk.wire();
					if (wire_chunk.is_whole()) {
						if (wire_chunk.wire->port_input) {
							Node node = factory.value(factory.ir().input(wire_chunk.wire->name));
							factory.suggest_name(node, wire_chunk.wire->name);
							factory.update_pending(pending, node);
						} else {
							DriveSpec driver = driver_map(DriveSpec(wire_chunk));
							check_undriven(driver, RTLIL::unescape_id(wire_chunk.wire->name));
							Node node = enqueue(driver);
							factory.suggest_name(node, wire_chunk.wire->name);
							factory.update_pending(pending, node);
						}
					} else {
						DriveChunkWire whole_wire(wire_chunk.wire, 0, wire_chunk.wire->width);
						Node node = factory.slice(enqueue(whole_wire), wire_chunk.offset, wire_chunk.width);
						factory.update_pending(pending, node);
					}
				} else if (chunk.is_port()) {
					DriveChunkPort port_chunk = chunk.port();
					if (port_chunk.is_whole()) {
						if (driver_map.celltypes.cell_output(port_chunk.cell->type, port_chunk.port)) {
							Node node = enqueue_cell(port_chunk.cell, port_chunk.port);
							factory.update_pending(pending, node);
						} else {
							DriveSpec driver = driver_map(DriveSpec(port_chunk));
							check_undriven(driver, RTLIL::unescape_id(port_chunk.cell->name) + " port " + RTLIL::unescape_id(port_chunk.port));
							factory.update_pending(pending, enqueue(driver));
						}
					} else {
						DriveChunkPort whole_port(port_chunk.cell, port_chunk.port, 0, GetSize(port_chunk.cell->connections().at(port_chunk.port)));
						Node node = factory.slice(enqueue(whole_port), port_chunk.offset, port_chunk.width);
						factory.update_pending(pending, node);
					}
				} else if (chunk.is_constant()) {
					Node node = factory.constant(chunk.constant());
					factory.suggest_name(node, "$const" + std::to_string(chunk.size()) + "b" + chunk.constant().as_string());
					factory.update_pending(pending, node);
				} else if (chunk.is_multiple()) {
					log_error("Signal %s has multiple drivers. This is not supported by the functional backend. "
						"If tristate drivers are used, call tristate -formal to avoid this error.\n", log_signal(chunk));
				} else if (chunk.is_none()) {
					undriven(log_signal(chunk));
				} else {
					log_error("unhandled drivespec: %s\n", log_signal(chunk));
					log_abort();
				}
			} else {
				log_abort();
			}
		}
	}
};

IR IR::from_module(Module *module) {
	IR ir;
    auto factory = ir.factory();
    FunctionalIRConstruction ctor(module, factory);
    ctor.process_queue();
    ir.topological_sort();
    ir.forward_buf();
    return ir;
}

void IR::topological_sort() {
    Graph::SccAdaptor compute_graph_scc(_graph);
    bool scc = false;
    std::vector<int> perm;
    TopoSortedSccs toposort(compute_graph_scc, [&](int *begin, int *end) {
        perm.insert(perm.end(), begin, end);
        if (end > begin + 1)
        {
            log_warning("Combinational loop:\n");
            for (int *i = begin; i != end; ++i) {
				Node node(_graph[*i]);
                log("- %s = %s\n", RTLIL::unescape_id(node.name()).c_str(), node.to_string().c_str());
			}
            log("\n");
            scc = true;
        }
    });
	for(const auto &[name, state]: _states)
		if(state.has_next_value())
			toposort.process(state.next_value().id());
	for(const auto &[name, output]: _outputs)
		if(output.has_value())
			toposort.process(output.value().id());
	// any nodes untouched by this point are dead code and will be removed by permute
    _graph.permute(perm);
    if(scc) log_error("The design contains combinational loops. This is not supported by the functional backend. "
		"Try `scc -select; simplemap; select -clear` to avoid this error.\n");
}

static IdString merge_name(IdString a, IdString b) {
	if(a[0] == '$' && b[0] == '\\')
		return b;
	else
		return a;
}

void IR::forward_buf() {
    std::vector<int> perm, alias;
    perm.clear();

    for (int i = 0; i < _graph.size(); ++i)
    {
        auto node = _graph[i];
        if (node.function().fn() == Fn::buf && node.arg(0).index() < i)
        {
            int target_index = alias[node.arg(0).index()];
            auto target_node = _graph[perm[target_index]];
			if(node.has_sparse_attr()) {
				if(target_node.has_sparse_attr()) {
					IdString id = merge_name(node.sparse_attr(), target_node.sparse_attr());
					target_node.sparse_attr() = id;
				} else {
					IdString id = node.sparse_attr();
					target_node.sparse_attr() = id;
				}
			}
            alias.push_back(target_index);
        }
        else
        {
            alias.push_back(GetSize(perm));
            perm.push_back(i);
        }
    }
    _graph.permute(perm, alias);
}

// Quoting routine to make error messages nicer
static std::string quote_fmt(const char *fmt)
{
	std::string r;
	for(const char *p = fmt; *p != 0; p++) {
		switch(*p) {
		case '\n': r += "\\n"; break;
		case '\t': r += "\\t"; break;
		case '"': r += "\\\""; break;
		case '\\': r += "\\\\"; break;
		default: r += *p; break;
		}
	}
	return r;
}

void Writer::print_impl(const char *fmt, vector<std::function<void()>> &fns)
{
	size_t next_index = 0;
	for(const char *p = fmt; *p != 0; p++)
		switch(*p) {
		case '{':
			if(*++p == '{') {
				*os << '{';
			} else {
				char *pe;
				size_t index = strtoul(p, &pe, 10);
				if(*pe != '}')
					log_error("invalid format string: expected {<number>}, {} or {{, got \"%s\": \"%s\"\n",
						quote_fmt(std::string(p - 1, pe - p + 2).c_str()).c_str(),
						quote_fmt(fmt).c_str());
				if(p == pe)
					index = next_index;
				else
					p = pe;
				if(index >= fns.size())
					log_error("invalid format string: index %zu out of bounds (%zu): \"%s\"\n", index, fns.size(), quote_fmt(fmt).c_str());
				fns[index]();
				next_index = index + 1;
			}
			break;
		case '}':
			p++;
			if(*p != '}')
				log_error("invalid format string: unescaped }: \"%s\"\n", quote_fmt(fmt).c_str());
			*os << '}';
			break;
		default:
			*os << *p;
		}
}

}
YOSYS_NAMESPACE_END
