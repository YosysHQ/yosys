/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2024  Emily Schmidt <emily@yosyshq.com>
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

#ifndef FUNCTIONALIR_H
#define FUNCTIONALIR_H

#include "kernel/yosys.h"
#include "kernel/functional.h"
#include "kernel/drivertools.h"
#include "kernel/mem.h"
#include "kernel/topo_scc.h"

USING_YOSYS_NAMESPACE
YOSYS_NAMESPACE_BEGIN

class FunctionalIR {
	enum class Fn {
		invalid,
		buf,
		slice,
		zero_extend,
		sign_extend,
		concat,
		add,
		sub,
		bitwise_and,
		bitwise_or,
		bitwise_xor,
		bitwise_not,
		reduce_and,
		reduce_or,
		reduce_xor,
		unary_minus,
		equal,
		not_equal,
		signed_greater_than,
		signed_greater_equal,
		unsigned_greater_than,
		unsigned_greater_equal,
		logical_shift_left,
		logical_shift_right,
		arithmetic_shift_right,
		mux,
		pmux,
		constant,
		input,
		state,
		multiple,
		undriven,
		memory_read,
		memory_write
	};
public:
	class Sort {
		std::variant<int, std::pair<int, int>> _v;
	public:
		explicit Sort(int width) : _v(width) { }
		Sort(int addr_width, int data_width) : _v(std::make_pair(addr_width, data_width)) { }
		bool is_signal() const { return _v.index() == 0; }
		bool is_memory() const { return _v.index() == 1; }
		int width() const { return std::get<0>(_v); }
		int addr_width() const { return std::get<1>(_v).first; }
		int data_width() const { return std::get<1>(_v).second; }
		bool operator==(Sort const& other) const { return _v == other._v; }
		unsigned int hash() const { return mkhash(_v); }
	};
private:
	class NodeData {
		Fn _fn;
		std::variant<
			std::monostate,
			RTLIL::Const,
			IdString,
			int
		> _extra;
	public:
		NodeData() : _fn(Fn::invalid) {}
		NodeData(Fn fn) : _fn(fn) {}
		template<class T> NodeData(Fn fn, T &&extra) : _fn(fn), _extra(std::forward<T>(extra)) {}
		Fn fn() const { return _fn; }
		const RTLIL::Const &as_const() const { return std::get<RTLIL::Const>(_extra); }
		IdString as_idstring() const { return std::get<IdString>(_extra); }
		int as_int() const { return std::get<int>(_extra); }
		int hash() const {
			return mkhash((unsigned int) _fn, mkhash(_extra));
		}
		bool operator==(NodeData const &other) const {
			return _fn == other._fn && _extra == other._extra;
		}
	};
	struct Attr {
		Sort sort;
	};
	using Graph = ComputeGraph<NodeData, Attr, IdString, std::pair<IdString, bool>>;
	Graph _graph;
	dict<IdString, Sort> _inputs;
	dict<IdString, Sort> _outputs;
	dict<IdString, Sort> _state;
	void add_input(IdString name, Sort sort) {
		auto [it, found] = _inputs.emplace(name, std::move(sort));
		if(found)
			log_assert(it->second == sort);
	}
	void add_state(IdString name, Sort sort) {
		auto [it, found] = _state.emplace(name, std::move(sort));
		if(found)
			log_assert(it->second == sort);
	}
	void add_output(IdString name, Sort sort) {
		auto [it, found] = _outputs.emplace(name, std::move(sort));
		if(found)
			log_assert(it->second == sort);
	}
public:
	class Factory;
	class Node {
		friend class Factory;
		friend class FunctionalIR;
		Graph::Ref _ref;
		Node(Graph::Ref ref) : _ref(ref) { }
		operator Graph::Ref() { return _ref; }
		template<class NodePrinter> struct PrintVisitor {
			NodePrinter np;
			PrintVisitor(NodePrinter np) : np(np) { }
			std::string buf(Node, Node n) { return "buf(" + np(n) + ")"; }
			std::string slice(Node, Node a, int, int offset, int out_width) { return "slice(" + np(a) + ", " + std::to_string(offset) + ", " + std::to_string(out_width) + ")"; }
			std::string zero_extend(Node, Node a, int, int out_width) { return "zero_extend(" + np(a) + ", " + std::to_string(out_width) + ")"; }
			std::string sign_extend(Node, Node a, int, int out_width) { return "sign_extend(" + np(a) + ", " + std::to_string(out_width) + ")"; }
			std::string concat(Node, Node a, int, Node b, int) { return "concat(" + np(a) + ", " + np(b) + ")"; }
			std::string add(Node, Node a, Node b, int) { return "add(" + np(a) + ", " + np(b) + ")"; }
			std::string sub(Node, Node a, Node b, int) { return "sub(" + np(a) + ", " + np(b) + ")"; }
			std::string bitwise_and(Node, Node a, Node b, int) { return "bitwise_and(" + np(a) + ", " + np(b) + ")"; }
			std::string bitwise_or(Node, Node a, Node b, int) { return "bitwise_or(" + np(a) + ", " + np(b) + ")"; }
			std::string bitwise_xor(Node, Node a, Node b, int) { return "bitwise_xor(" + np(a) + ", " + np(b) + ")"; }
			std::string bitwise_not(Node, Node a, int) { return "bitwise_not(" + np(a) + ")"; }
			std::string unary_minus(Node, Node a, int) { return "unary_minus(" + np(a) + ")"; }
			std::string reduce_and(Node, Node a, int) { return "reduce_and(" + np(a) + ")"; }
			std::string reduce_or(Node, Node a, int) { return "reduce_or(" + np(a) + ")"; }
			std::string reduce_xor(Node, Node a, int) { return "reduce_xor(" + np(a) + ")"; }
			std::string equal(Node, Node a, Node b, int) { return "equal(" + np(a) + ", " + np(b) + ")"; }
			std::string not_equal(Node, Node a, Node b, int) { return "not_equal(" + np(a) + ", " + np(b) + ")"; }
			std::string signed_greater_than(Node, Node a, Node b, int) { return "signed_greater_than(" + np(a) + ", " + np(b) + ")"; }
			std::string signed_greater_equal(Node, Node a, Node b, int) { return "signed_greater_equal(" + np(a) + ", " + np(b) + ")"; }
			std::string unsigned_greater_than(Node, Node a, Node b, int) { return "unsigned_greater_than(" + np(a) + ", " + np(b) + ")"; }
			std::string unsigned_greater_equal(Node, Node a, Node b, int) { return "unsigned_greater_equal(" + np(a) + ", " + np(b) + ")"; }
			std::string logical_shift_left(Node, Node a, Node b, int, int) { return "logical_shift_left(" + np(a) + ", " + np(b) + ")"; }
			std::string logical_shift_right(Node, Node a, Node b, int, int) { return "logical_shift_right(" + np(a) + ", " + np(b) + ")"; }
			std::string arithmetic_shift_right(Node, Node a, Node b, int, int) { return "arithmetic_shift_right(" + np(a) + ", " + np(b) + ")"; }
			std::string mux(Node, Node a, Node b, Node s, int) { return "mux(" + np(a) + ", " + np(b) + ", " + np(s) + ")"; }
			std::string pmux(Node, Node a, Node b, Node s, int, int) { return "pmux(" + np(a) + ", " + np(b) + ", " + np(s) + ")"; }
			std::string constant(Node, RTLIL::Const value) { return "constant(" + value.as_string() + ")"; }
			std::string input(Node, IdString name) { return "input(" + name.str() + ")"; }
			std::string state(Node, IdString name) { return "state(" + name.str() + ")"; }
			std::string memory_read(Node, Node mem, Node addr, int, int) { return "memory_read(" + np(mem) + ", " + np(addr) + ")"; }
			std::string memory_write(Node, Node mem, Node addr, Node data, int, int) { return "memory_write(" + np(mem) + ", " + np(addr) + ", " + np(data) + ")"; }
			std::string undriven(Node, int width) { return "undriven(" + std::to_string(width) + ")"; }
		};
	public:
		int id() const { return _ref.index(); }
		IdString name() const {
			if(_ref.has_sparse_attr())
				return _ref.sparse_attr();
			else
				return std::string("\\n") + std::to_string(id());
		}
		Sort sort() const { return _ref.attr().sort; }
		int width() const { return sort().width(); }
		Node arg(int n) const { return Node(_ref.arg(n)); }
		template<class Visitor> auto visit(Visitor v) const
		{
			switch(_ref.function().fn()) {
			case Fn::invalid: log_error("invalid node in visit"); break;
			case Fn::buf: return v.buf(*this, arg(0)); break;
			case Fn::slice: return v.slice(*this, arg(0), arg(0).width(), _ref.function().as_int(), sort().width()); break;
			case Fn::zero_extend: return v.zero_extend(*this, arg(0), arg(0).width(), width()); break;
			case Fn::sign_extend: return v.sign_extend(*this, arg(0), arg(0).width(), width()); break;
			case Fn::concat: return v.concat(*this, arg(0), arg(0).width(), arg(1), arg(1).width()); break;
			case Fn::add: return v.add(*this, arg(0), arg(1), sort().width()); break;
			case Fn::sub: return v.sub(*this, arg(0), arg(1), sort().width()); break;
			case Fn::bitwise_and: return v.bitwise_and(*this, arg(0), arg(1), sort().width()); break;
			case Fn::bitwise_or: return v.bitwise_or(*this, arg(0), arg(1), sort().width()); break;
			case Fn::bitwise_xor: return v.bitwise_xor(*this, arg(0), arg(1), sort().width()); break;
			case Fn::bitwise_not: return v.bitwise_not(*this, arg(0), sort().width()); break;
			case Fn::unary_minus: return v.bitwise_not(*this, arg(0), sort().width()); break;
			case Fn::reduce_and: return v.reduce_and(*this, arg(0), arg(0).width()); break;
			case Fn::reduce_or: return v.reduce_or(*this, arg(0), arg(0).width()); break;
			case Fn::reduce_xor: return v.reduce_xor(*this, arg(0), arg(0).width()); break;
			case Fn::equal: return v.equal(*this, arg(0), arg(1), arg(0).width()); break;
			case Fn::not_equal: return v.not_equal(*this, arg(0), arg(1), arg(0).width()); break;
			case Fn::signed_greater_than: return v.signed_greater_than(*this, arg(0), arg(1), arg(0).width()); break; 
			case Fn::signed_greater_equal: return v.signed_greater_equal(*this, arg(0), arg(1), arg(0).width()); break;
			case Fn::unsigned_greater_than: return v.unsigned_greater_than(*this, arg(0), arg(1), arg(0).width()); break; 
			case Fn::unsigned_greater_equal: return v.unsigned_greater_equal(*this, arg(0), arg(1), arg(0).width()); break;
			case Fn::logical_shift_left: return v.logical_shift_left(*this, arg(0), arg(1), arg(0).width(), arg(1).width()); break;
			case Fn::logical_shift_right: return v.logical_shift_right(*this, arg(0), arg(1), arg(0).width(), arg(1).width()); break;
			case Fn::arithmetic_shift_right: return v.arithmetic_shift_right(*this, arg(0), arg(1), arg(0).width(), arg(1).width()); break;
			case Fn::mux: return v.mux(*this, arg(0), arg(1), arg(2), arg(0).width()); break;
			case Fn::pmux: return v.pmux(*this, arg(0), arg(1), arg(2), arg(0).width(), arg(2).width()); break;
			case Fn::constant: return v.constant(*this, _ref.function().as_const()); break;
			case Fn::input: return v.input(*this, _ref.function().as_idstring()); break;
			case Fn::state: return v.state(*this, _ref.function().as_idstring()); break;
			case Fn::memory_read: return v.memory_read(*this, arg(0), arg(1), arg(1).width(), width()); break;
			case Fn::memory_write: return v.memory_write(*this, arg(0), arg(1), arg(2), arg(1).width(), arg(2).width()); break;
			case Fn::multiple: log_error("multiple in visit"); break;
			case Fn::undriven: return v.undriven(*this, width()); break;
			}
		}
		template<class NodePrinter> std::string to_string(NodePrinter np)
		{
			return visit(PrintVisitor(np));
		}
		/* TODO: delete */ int size() const { return sort().width(); }
	};
	class Factory {
		FunctionalIR &_ir;
		friend class FunctionalIR;
		explicit Factory(FunctionalIR &ir) : _ir(ir) {}
		Node add(NodeData &&fn, Sort &&sort, std::initializer_list<Node> args) {
			Graph::Ref ref = _ir._graph.add(std::move(fn), {std::move(sort)});
			for (auto arg : args)
				ref.append_arg(Graph::Ref(arg));
			return ref;
		}
		void check_basic_binary(Node const &a, Node const &b) { log_assert(a.sort().is_signal() && a.sort() == b.sort()); }
		void check_shift(Node const &a, Node const &b) { log_assert(a.sort().is_signal() && b.sort().is_signal()); }
		void check_unary(Node const &a) { log_assert(a.sort().is_signal()); }
	public:
		Node slice(Node a, int, int offset, int out_width) {
			log_assert(a.sort().is_signal() && offset + out_width <= a.sort().width());
			return add(NodeData(Fn::slice, offset), Sort(out_width), {a});
		}
		Node extend(Node a, int, int out_width, bool is_signed) {
			log_assert(a.sort().is_signal() && a.sort().width() < out_width);
			if(is_signed)
				return add(Fn::sign_extend, Sort(out_width), {a});
			else
				return add(Fn::zero_extend, Sort(out_width), {a});
		}
		Node concat(Node a, int, Node b, int) {
			log_assert(a.sort().is_signal() && b.sort().is_signal());
			return add(Fn::concat, Sort(a.sort().width() + b.sort().width()), {a, b});
		}
		Node add(Node a, Node b, int) { check_basic_binary(a, b); return add(Fn::add, a.sort(), {a, b}); }
		Node sub(Node a, Node b, int) { check_basic_binary(a, b); return add(Fn::sub, a.sort(), {a, b}); }
		Node bitwise_and(Node a, Node b, int) { check_basic_binary(a, b); return add(Fn::bitwise_and, a.sort(), {a, b}); }
		Node bitwise_or(Node a, Node b, int) { check_basic_binary(a, b); return add(Fn::bitwise_or, a.sort(), {a, b}); }
		Node bitwise_xor(Node a, Node b, int) { check_basic_binary(a, b); return add(Fn::bitwise_xor, a.sort(), {a, b}); }
		Node bitwise_not(Node a, int) { check_unary(a); return add(Fn::bitwise_not, a.sort(), {a}); }
		Node unary_minus(Node a, int) { check_unary(a); return add(Fn::unary_minus, a.sort(), {a}); }
		Node reduce_and(Node a, int) { check_unary(a); return add(Fn::reduce_and, Sort(1), {a}); }
		Node reduce_or(Node a, int) { check_unary(a); return add(Fn::reduce_or, Sort(1), {a}); }
		Node reduce_xor(Node a, int) { check_unary(a); return add(Fn::reduce_xor, Sort(1), {a}); }
		Node equal(Node a, Node b, int) { check_basic_binary(a, b); return add(Fn::equal, Sort(1), {a, b}); }
		Node not_equal(Node a, Node b, int) { check_basic_binary(a, b); return add(Fn::not_equal, Sort(1), {a, b}); }
		Node signed_greater_than(Node a, Node b, int) { check_basic_binary(a, b); return add(Fn::signed_greater_than, Sort(1), {a, b}); }
		Node signed_greater_equal(Node a, Node b, int) { check_basic_binary(a, b); return add(Fn::signed_greater_equal, Sort(1), {a, b}); }
		Node unsigned_greater_than(Node a, Node b, int) { check_basic_binary(a, b); return add(Fn::unsigned_greater_than, Sort(1), {a, b}); }
		Node unsigned_greater_equal(Node a, Node b, int) { check_basic_binary(a, b); return add(Fn::unsigned_greater_equal, Sort(1), {a, b}); }
		Node logical_shift_left(Node a, Node b, int, int) { check_shift(a, b); return add(Fn::logical_shift_left, a.sort(), {a, b}); }
		Node logical_shift_right(Node a, Node b, int, int) { check_shift(a, b); return add(Fn::logical_shift_right, a.sort(), {a, b}); }
		Node arithmetic_shift_right(Node a, Node b, int, int) { check_shift(a, b); return add(Fn::arithmetic_shift_right, a.sort(), {a, b}); }
		Node mux(Node a, Node b, Node s, int) {
			log_assert(a.sort().is_signal() && a.sort() == b.sort() && s.sort() == Sort(1));
			return add(Fn::mux, a.sort(), {a, b, s});
		}
		Node pmux(Node a, Node b, Node s, int, int) {
			log_assert(a.sort().is_signal() && b.sort().is_signal() && s.sort().is_signal() && a.sort().width() * s.sort().width() == b.sort().width());
			return add(Fn::pmux, a.sort(), {a, b, s});
		}
		Node memory_read(Node mem, Node addr, int, int) {
			log_assert(mem.sort().is_memory() && addr.sort().is_signal() && mem.sort().addr_width() == addr.sort().width());
			return add(Fn::memory_read, Sort(mem.sort().data_width()), {mem, addr});
		}
		Node memory_write(Node mem, Node addr, Node data, int, int) {
			log_assert(mem.sort().is_memory() && addr.sort().is_signal() && data.sort().is_signal() &&
				mem.sort().addr_width() == addr.sort().width() && mem.sort().data_width() == data.sort().width());
			return add(Fn::memory_write, mem.sort(), {mem, addr, data});
		}
		Node constant(RTLIL::Const value) {
			return add(NodeData(Fn::constant, std::move(value)), Sort(value.size()), {});
		}
		Node create_pending(int width) {
			return add(Fn::buf, Sort(width), {});
		}
		void update_pending(Node node, Node value) {
			log_assert(node._ref.function() == Fn::buf && node._ref.size() == 0 && node.sort() == value.sort());
			node._ref.append_arg(value._ref);
		} 
		Node input(IdString name, int width) {
			_ir.add_input(name, Sort(width));
			return add(NodeData(Fn::input, name), Sort(width), {});
		}
		Node state(IdString name, int width) {
			_ir.add_state(name, Sort(width));
			return add(NodeData(Fn::state, name), Sort(width), {});
		}
		Node state_memory(IdString name, int addr_width, int data_width) {
			_ir.add_state(name, Sort(addr_width, data_width));
			return add(NodeData(Fn::state, name), Sort(addr_width, data_width), {});
		}
		Node cell_output(Node node, IdString, IdString, int) {
			return node;
		}
		Node multiple(vector<Node> args, int width) {
			auto node = add(Fn::multiple, Sort(width), {});
			for(const auto &arg : args)
				node._ref.append_arg(arg._ref);
			return node;
		}
		Node undriven(int width) {
			return add(Fn::undriven, Sort(width), {});
		}
		void declare_output(Node node, IdString name, int width) {
			_ir.add_output(name, Sort(width));
			node._ref.assign_key({name, false});
		}
		void declare_state(Node node, IdString name, int width) {
			_ir.add_state(name, Sort(width));
			node._ref.assign_key({name, true});
		}
		void declare_state_memory(Node node, IdString name, int addr_width, int data_width) {
			_ir.add_state(name, Sort(addr_width, data_width));
			node._ref.assign_key({name, true});
		}
		void suggest_name(Node node, IdString name) {
			node._ref.sparse_attr() = name;
		}

		/* TODO delete this later*/
		Node eq(Node a, Node b, int) { return equal(a, b, 0); }
		Node ne(Node a, Node b, int) { return not_equal(a, b, 0); }
		Node gt(Node a, Node b, int) { return signed_greater_than(a, b, 0); }
		Node ge(Node a, Node b, int) { return signed_greater_equal(a, b, 0); }
		Node ugt(Node a, Node b, int) { return unsigned_greater_than(a, b, 0); }
		Node uge(Node a, Node b, int) { return unsigned_greater_equal(a, b, 0); }
		Node neg(Node a, int) { return unary_minus(a, 0); }
	};
	static FunctionalIR from_module(Module *module);
	Factory factory() { return Factory(*this); }
	int size() const { return _graph.size(); }
	Node operator[](int i) { return _graph[i]; }
	void topological_sort();
	void forward_buf();
	dict<IdString, Sort> inputs() const { return _inputs; }
	dict<IdString, Sort> outputs() const { return _outputs; }
	dict<IdString, Sort> state() const { return _state; }
	Node get_output_node(IdString name) { return _graph({name, false}); }
	Node get_state_next_node(IdString name) { return _graph({name, true}); }
	class Iterator {
		friend class FunctionalIR;
		FunctionalIR &_ir;
		int _index;
		Iterator(FunctionalIR &ir, int index) : _ir(ir), _index(index) {}
	public:
		Node operator*() { return _ir._graph[_index]; }
		Iterator &operator++() { _index++; return *this; }
		bool operator!=(Iterator const &other) const { return _index != other._index; }
	};
	Iterator begin() { return Iterator(*this, 0); }
	Iterator end() { return Iterator(*this, _graph.size()); }
};

YOSYS_NAMESPACE_END

#endif
