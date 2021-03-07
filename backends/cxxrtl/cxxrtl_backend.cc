/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2019-2020  whitequark <whitequark@whitequark.org>
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

#include "kernel/rtlil.h"
#include "kernel/register.h"
#include "kernel/sigtools.h"
#include "kernel/utils.h"
#include "kernel/celltypes.h"
#include "kernel/mem.h"
#include "kernel/log.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// [[CITE]]
// Peter Eades; Xuemin Lin; W. F. Smyth, "A Fast Effective Heuristic For The Feedback Arc Set Problem"
// Information Processing Letters, Vol. 47, pp 319-323, 1993
// https://pdfs.semanticscholar.org/c7ed/d9acce96ca357876540e19664eb9d976637f.pdf

// A topological sort (on a cell/wire graph) is always possible in a fully flattened RTLIL design without
// processes or logic loops where every wire has a single driver. Logic loops are illegal in RTLIL and wires
// with multiple drivers can be split by the `splitnets` pass; however, interdependencies between processes
// or module instances can create strongly connected components without introducing evaluation nondeterminism.
// We wish to support designs with such benign SCCs (as well as designs with multiple drivers per wire), so
// we sort the graph in a way that minimizes feedback arcs. If there are no feedback arcs in the sorted graph,
// then a more efficient evaluation method is possible, since eval() will always immediately converge.
template<class T>
struct Scheduler {
	struct Vertex {
		T *data;
		Vertex *prev, *next;
		pool<Vertex*, hash_ptr_ops> preds, succs;

		Vertex() : data(NULL), prev(this), next(this) {}
		Vertex(T *data) : data(data), prev(NULL), next(NULL) {}

		bool empty() const
		{
			log_assert(data == NULL);
			if (next == this) {
				log_assert(prev == next);
				return true;
			}
			return false;
		}

		void link(Vertex *list)
		{
			log_assert(prev == NULL && next == NULL);
			next = list;
			prev = list->prev;
			list->prev->next = this;
			list->prev = this;
		}

		void unlink()
		{
			log_assert(prev->next == this && next->prev == this);
			prev->next = next;
			next->prev = prev;
			next = prev = NULL;
		}

		int delta() const
		{
			return succs.size() - preds.size();
		}
	};

	std::vector<Vertex*> vertices;
	Vertex *sources = new Vertex;
	Vertex *sinks = new Vertex;
	dict<int, Vertex*> bins;

	~Scheduler()
	{
		delete sources;
		delete sinks;
		for (auto bin : bins)
			delete bin.second;
		for (auto vertex : vertices)
			delete vertex;
	}

	Vertex *add(T *data)
	{
		Vertex *vertex = new Vertex(data);
		vertices.push_back(vertex);
		return vertex;
	}

	void relink(Vertex *vertex)
	{
		if (vertex->succs.empty())
			vertex->link(sinks);
		else if (vertex->preds.empty())
			vertex->link(sources);
		else {
			int delta = vertex->delta();
			if (!bins.count(delta))
				bins[delta] = new Vertex;
			vertex->link(bins[delta]);
		}
	}

	Vertex *remove(Vertex *vertex)
	{
		vertex->unlink();
		for (auto pred : vertex->preds) {
			if (pred == vertex)
				continue;
			log_assert(pred->succs[vertex]);
			pred->unlink();
			pred->succs.erase(vertex);
			relink(pred);
		}
		for (auto succ : vertex->succs) {
			if (succ == vertex)
				continue;
			log_assert(succ->preds[vertex]);
			succ->unlink();
			succ->preds.erase(vertex);
			relink(succ);
		}
		vertex->preds.clear();
		vertex->succs.clear();
		return vertex;
	}

	std::vector<Vertex*> schedule()
	{
		std::vector<Vertex*> s1, s2r;
		for (auto vertex : vertices)
			relink(vertex);
		bool bins_empty = false;
		while (!(sinks->empty() && sources->empty() && bins_empty)) {
			while (!sinks->empty())
				s2r.push_back(remove(sinks->next));
			while (!sources->empty())
				s1.push_back(remove(sources->next));
			// Choosing u in this implementation isn't O(1), but the paper handwaves which data structure they suggest
			// using to get O(1) relinking *and* find-max-key ("it is clear"... no it isn't), so this code uses a very
			// naive implementation of find-max-key.
			bins_empty = true;
			bins.template sort<std::greater<int>>();
			for (auto bin : bins) {
				if (!bin.second->empty()) {
					bins_empty = false;
					s1.push_back(remove(bin.second->next));
					break;
				}
			}
		}
		s1.insert(s1.end(), s2r.rbegin(), s2r.rend());
		return s1;
	}
};

bool is_unary_cell(RTLIL::IdString type)
{
	return type.in(
		ID($not), ID($logic_not), ID($reduce_and), ID($reduce_or), ID($reduce_xor), ID($reduce_xnor), ID($reduce_bool),
		ID($pos), ID($neg));
}

bool is_binary_cell(RTLIL::IdString type)
{
	return type.in(
		ID($and), ID($or), ID($xor), ID($xnor), ID($logic_and), ID($logic_or),
		ID($shl), ID($sshl), ID($shr), ID($sshr), ID($shift), ID($shiftx),
		ID($eq), ID($ne), ID($eqx), ID($nex), ID($gt), ID($ge), ID($lt), ID($le),
		ID($add), ID($sub), ID($mul), ID($div), ID($mod));
}

bool is_extending_cell(RTLIL::IdString type)
{
	return !type.in(
		ID($logic_not), ID($logic_and), ID($logic_or),
		ID($reduce_and), ID($reduce_or), ID($reduce_xor), ID($reduce_xnor), ID($reduce_bool));
}

bool is_inlinable_cell(RTLIL::IdString type)
{
	return is_unary_cell(type) || is_binary_cell(type) || type.in(
		ID($mux), ID($concat), ID($slice), ID($pmux));
}

bool is_ff_cell(RTLIL::IdString type)
{
	return type.in(
		ID($dff), ID($dffe), ID($sdff), ID($sdffe), ID($sdffce),
		ID($adff), ID($adffe), ID($dffsr), ID($dffsre),
		ID($dlatch), ID($adlatch), ID($dlatchsr), ID($sr));
}

bool is_internal_cell(RTLIL::IdString type)
{
	return !type.isPublic() && !type.begins_with("$paramod");
}

bool is_effectful_cell(RTLIL::IdString type)
{
	return type == ID($memwr) || type.isPublic();
}

bool is_cxxrtl_blackbox_cell(const RTLIL::Cell *cell)
{
	RTLIL::Module *cell_module = cell->module->design->module(cell->type);
	log_assert(cell_module != nullptr);
	return cell_module->get_bool_attribute(ID(cxxrtl_blackbox));
}

enum class CxxrtlPortType {
	UNKNOWN = 0, // or mixed comb/sync
	COMB = 1,
	SYNC = 2,
};

CxxrtlPortType cxxrtl_port_type(RTLIL::Module *module, RTLIL::IdString port)
{
	RTLIL::Wire *output_wire = module->wire(port);
	log_assert(output_wire != nullptr);
	bool is_comb = output_wire->get_bool_attribute(ID(cxxrtl_comb));
	bool is_sync = output_wire->get_bool_attribute(ID(cxxrtl_sync));
	if (is_comb && is_sync)
		log_cmd_error("Port `%s.%s' is marked as both `cxxrtl_comb` and `cxxrtl_sync`.\n",
		              log_id(module), log_signal(output_wire));
	else if (is_comb)
		return CxxrtlPortType::COMB;
	else if (is_sync)
		return CxxrtlPortType::SYNC;
	return CxxrtlPortType::UNKNOWN;
}

CxxrtlPortType cxxrtl_port_type(const RTLIL::Cell *cell, RTLIL::IdString port)
{
	RTLIL::Module *cell_module = cell->module->design->module(cell->type);
	if (cell_module == nullptr || !cell_module->get_bool_attribute(ID(cxxrtl_blackbox)))
		return CxxrtlPortType::UNKNOWN;
	return cxxrtl_port_type(cell_module, port);
}

bool is_cxxrtl_comb_port(const RTLIL::Cell *cell, RTLIL::IdString port)
{
	return cxxrtl_port_type(cell, port) == CxxrtlPortType::COMB;
}

bool is_cxxrtl_sync_port(const RTLIL::Cell *cell, RTLIL::IdString port)
{
	return cxxrtl_port_type(cell, port) == CxxrtlPortType::SYNC;
}

struct FlowGraph {
	struct Node {
		enum class Type {
			CONNECT,
			CELL_SYNC,
			CELL_EVAL,
			PROCESS_SYNC,
			PROCESS_CASE,
		};

		Type type;
		RTLIL::SigSig connect = {};
		const RTLIL::Cell *cell = NULL;
		const RTLIL::Process *process = NULL;
	};

	std::vector<Node*> nodes;
	dict<const RTLIL::Wire*, pool<Node*, hash_ptr_ops>> wire_comb_defs, wire_sync_defs, wire_uses;
	dict<Node*, pool<const RTLIL::Wire*>, hash_ptr_ops> node_comb_defs, node_sync_defs, node_uses;
	dict<const RTLIL::Wire*, bool> wire_def_inlinable;
	dict<const RTLIL::Wire*, dict<Node*, bool, hash_ptr_ops>> wire_use_inlinable;
	dict<RTLIL::SigBit, bool> bit_has_state;

	~FlowGraph()
	{
		for (auto node : nodes)
			delete node;
	}

	void add_defs(Node *node, const RTLIL::SigSpec &sig, bool is_ff, bool inlinable)
	{
		for (auto chunk : sig.chunks())
			if (chunk.wire) {
				if (is_ff) {
					// A sync def means that a wire holds design state because it is driven directly by
					// a flip-flop output. Such a wire can never be unbuffered.
					wire_sync_defs[chunk.wire].insert(node);
					node_sync_defs[node].insert(chunk.wire);
				} else {
					// A comb def means that a wire doesn't hold design state. It might still be connected,
					// indirectly, to a flip-flop output.
					wire_comb_defs[chunk.wire].insert(node);
					node_comb_defs[node].insert(chunk.wire);
				}
			}
		for (auto bit : sig.bits())
			bit_has_state[bit] |= is_ff;
		// Only comb defs of an entire wire in the right order can be inlined.
		if (!is_ff && sig.is_wire())
			wire_def_inlinable[sig.as_wire()] = inlinable;
	}

	void add_uses(Node *node, const RTLIL::SigSpec &sig)
	{
		for (auto chunk : sig.chunks())
			if (chunk.wire) {
				wire_uses[chunk.wire].insert(node);
				node_uses[node].insert(chunk.wire);
				// Only a single use of an entire wire in the right order can be inlined. (But the use can include
				// other chunks.) This is tracked per-node because a wire used by multiple nodes can still be inlined
				// if all but one of those nodes is dead.
				if (!wire_use_inlinable[chunk.wire].count(node))
					wire_use_inlinable[chunk.wire][node] = true;
				else
					wire_use_inlinable[chunk.wire][node] = false;
			}
	}

	bool is_inlinable(const RTLIL::Wire *wire) const
	{
		// Can the wire be inlined at all?
		if (wire_def_inlinable.count(wire))
			return wire_def_inlinable.at(wire);
		return false;
	}

	bool is_inlinable(const RTLIL::Wire *wire, const pool<Node*, hash_ptr_ops> &nodes) const
	{
		// Can the wire be inlined, knowing that the given nodes are reachable?
		if (nodes.size() != 1)
			return false;
		Node *node = *nodes.begin();
		log_assert(node_uses.at(node).count(wire));
		if (is_inlinable(wire) && wire_use_inlinable.count(wire) && wire_use_inlinable.at(wire).count(node))
			return wire_use_inlinable.at(wire).at(node);
		return false;
	}

	// Connections
	void add_connect_defs_uses(Node *node, const RTLIL::SigSig &conn)
	{
		add_defs(node, conn.first, /*is_ff=*/false, /*inlinable=*/true);
		add_uses(node, conn.second);
	}

	Node *add_node(const RTLIL::SigSig &conn)
	{
		Node *node = new Node;
		node->type = Node::Type::CONNECT;
		node->connect = conn;
		nodes.push_back(node);
		add_connect_defs_uses(node, conn);
		return node;
	}

	// Cells
	void add_cell_sync_defs(Node *node, const RTLIL::Cell *cell)
	{
		// To understand why this node type is necessary and why it produces comb defs, consider a cell
		// with input \i and sync output \o, used in a design such that \i is connected to \o. This does
		// not result in a feedback arc because the output is synchronous. However, a naive implementation
		// of code generation for cells that assigns to inputs, evaluates cells, assigns from outputs
		// would not be able to immediately converge...
		//
		//   wire<1> i_tmp;
		//   cell->p_i = i_tmp.curr;
		//   cell->eval();
		//   i_tmp.next = cell->p_o.curr;
		//
		// ... since the wire connecting the input and output ports would not be localizable. To solve
		// this, the cell is split into two scheduling nodes; one exclusively for sync outputs, and
		// another for inputs and all non-sync outputs. This way the generated code can be rearranged...
		//
		//   value<1> i_tmp;
		//   i_tmp = cell->p_o.curr;
		//   cell->p_i = i_tmp;
		//   cell->eval();
		//
		// eliminating the unnecessary delta cycle. Conceptually, the CELL_SYNC node type is a series of
		// connections of the form `connect \lhs \cell.\sync_output`; the right-hand side of these is not
		// expressible as a wire in RTLIL. If it was expressible, then `\cell.\sync_output` would have
		// a sync def, and this node would be an ordinary CONNECT node, with `\lhs` having a comb def.
		// Because it isn't, a special node type is used, the right-hand side does not appear anywhere,
		// and the left-hand side has a comb def.
		for (auto conn : cell->connections())
			if (cell->output(conn.first))
				if (is_cxxrtl_sync_port(cell, conn.first)) {
					// See note regarding inlinability below.
					add_defs(node, conn.second, /*is_ff=*/false, /*inlinable=*/false);
				}
	}

	void add_cell_eval_defs_uses(Node *node, const RTLIL::Cell *cell)
	{
		for (auto conn : cell->connections()) {
			if (cell->output(conn.first)) {
				if (is_inlinable_cell(cell->type))
					add_defs(node, conn.second, /*is_ff=*/false, /*inlinable=*/true);
				else if (is_ff_cell(cell->type) || (cell->type == ID($memrd) && cell->getParam(ID::CLK_ENABLE).as_bool()))
					add_defs(node, conn.second, /*is_ff=*/true,  /*inlinable=*/false);
				else if (is_internal_cell(cell->type))
					add_defs(node, conn.second, /*is_ff=*/false, /*inlinable=*/false);
				else if (!is_cxxrtl_sync_port(cell, conn.first)) {
					// Although at first it looks like outputs of user-defined cells may always be inlined, the reality is
					// more complex. Fully sync outputs produce no defs and so don't participate in inlining. Fully comb
					// outputs are assigned in a different way depending on whether the cell's eval() immediately converged.
					// Unknown/mixed outputs could be inlined, but should be rare in practical designs and don't justify
					// the infrastructure required to inline outputs of cells with many of them.
					add_defs(node, conn.second, /*is_ff=*/false, /*inlinable=*/false);
				}
			}
			if (cell->input(conn.first))
				add_uses(node, conn.second);
		}
	}

	Node *add_node(const RTLIL::Cell *cell)
	{
		log_assert(cell->known());

		bool has_fully_sync_outputs = false;
		for (auto conn : cell->connections())
			if (cell->output(conn.first) && is_cxxrtl_sync_port(cell, conn.first)) {
				has_fully_sync_outputs = true;
				break;
			}
		if (has_fully_sync_outputs) {
			Node *node = new Node;
			node->type = Node::Type::CELL_SYNC;
			node->cell = cell;
			nodes.push_back(node);
			add_cell_sync_defs(node, cell);
		}

		Node *node = new Node;
		node->type = Node::Type::CELL_EVAL;
		node->cell = cell;
		nodes.push_back(node);
		add_cell_eval_defs_uses(node, cell);
		return node;
	}

	// Processes
	void add_case_rule_defs_uses(Node *node, const RTLIL::CaseRule *case_)
	{
		for (auto &action : case_->actions) {
			add_defs(node, action.first, /*is_ff=*/false, /*inlinable=*/false);
			add_uses(node, action.second);
		}
		for (auto sub_switch : case_->switches) {
			add_uses(node, sub_switch->signal);
			for (auto sub_case : sub_switch->cases) {
				for (auto &compare : sub_case->compare)
					add_uses(node, compare);
				add_case_rule_defs_uses(node, sub_case);
			}
		}
	}

	void add_sync_rules_defs_uses(Node *node, const RTLIL::Process *process)
	{
		for (auto sync : process->syncs)
			for (auto action : sync->actions) {
				if (sync->type == RTLIL::STp || sync->type == RTLIL::STn || sync->type == RTLIL::STe)
				  add_defs(node, action.first, /*is_ff=*/true,  /*inlinable=*/false);
				else
					add_defs(node, action.first, /*is_ff=*/false, /*inlinable=*/false);
				add_uses(node, action.second);
			}
	}

	Node *add_node(const RTLIL::Process *process)
	{
		Node *node = new Node;
		node->type = Node::Type::PROCESS_SYNC;
		node->process = process;
		nodes.push_back(node);
		add_sync_rules_defs_uses(node, process);

		node = new Node;
		node->type = Node::Type::PROCESS_CASE;
		node->process = process;
		nodes.push_back(node);
		add_case_rule_defs_uses(node, &process->root_case);
		return node;
	}
};

std::vector<std::string> split_by(const std::string &str, const std::string &sep)
{
	std::vector<std::string> result;
	size_t prev = 0;
	while (true) {
		size_t curr = str.find_first_of(sep, prev);
		if (curr == std::string::npos) {
			std::string part = str.substr(prev);
			if (!part.empty()) result.push_back(part);
			break;
		} else {
			std::string part = str.substr(prev, curr - prev);
			if (!part.empty()) result.push_back(part);
			prev = curr + 1;
		}
	}
	return result;
}

std::string escape_cxx_string(const std::string &input)
{
	std::string output = "\"";
	for (auto c : input) {
		if (::isprint(c)) {
			if (c == '\\')
				output.push_back('\\');
			output.push_back(c);
		} else {
			char l = c & 0xf, h = (c >> 4) & 0xf;
			output.append("\\x");
			output.push_back((h < 10 ? '0' + h : 'a' + h - 10));
			output.push_back((l < 10 ? '0' + l : 'a' + l - 10));
		}
	}
	output.push_back('"');
	if (output.find('\0') != std::string::npos) {
		output.insert(0, "std::string {");
		output.append(stringf(", %zu}", input.size()));
	}
	return output;
}

template<class T>
std::string get_hdl_name(T *object)
{
	if (object->has_attribute(ID::hdlname))
		return object->get_string_attribute(ID::hdlname);
	else
		return object->name.str().substr(1);
}

struct WireType {
	enum Type {
		// Non-referenced wire; is not a part of the design.
		UNUSED,
		// Double-buffered wire; is a class member, and holds design state.
		BUFFERED,
		// Single-buffered wire; is a class member, but holds no state.
		MEMBER,
		// Single-buffered wire; is a class member, and is computed on demand.
		OUTLINE,
		// Local wire; is a local variable in eval method.
		LOCAL,
		// Inline wire; is an unnamed temporary in eval method.
		INLINE,
		// Alias wire; is replaced with aliasee, except in debug info.
		ALIAS,
		// Const wire; is replaced with constant, except in debug info.
		CONST,
	};

	Type type = UNUSED;
	const RTLIL::Cell *cell_subst = nullptr; // for INLINE
	RTLIL::SigSpec sig_subst = {}; // for INLINE, ALIAS, and CONST

	WireType() = default;

	WireType(Type type) : type(type) {
		log_assert(type == UNUSED || type == BUFFERED || type == MEMBER || type == OUTLINE || type == LOCAL);
	}

	WireType(Type type, const RTLIL::Cell *cell) : type(type), cell_subst(cell) {
		log_assert(type == INLINE && is_inlinable_cell(cell->type));
	}

	WireType(Type type, RTLIL::SigSpec sig) : type(type), sig_subst(sig) {
		log_assert(type == INLINE || (type == ALIAS && sig.is_wire()) || (type == CONST && sig.is_fully_const()));
	}

	bool is_buffered() const { return type == BUFFERED; }
	bool is_member() const { return type == BUFFERED || type == MEMBER || type == OUTLINE; }
	bool is_outline() const { return type == OUTLINE; }
	bool is_named() const { return is_member() || type == LOCAL; }
	bool is_local() const { return type == LOCAL || type == INLINE; }
	bool is_exact() const { return type == ALIAS || type == CONST; }
};

// Tests for a SigSpec that is a valid clock input, clocks have to have a backing wire and be a single bit
// using this instead of sig.is_wire() solves issues when the clock is a slice instead of a full wire
bool is_valid_clock(const RTLIL::SigSpec& sig) {
	return sig.is_chunk() && sig.is_bit() && sig[0].wire;
}

struct CxxrtlWorker {
	bool split_intf = false;
	std::string intf_filename;
	std::string design_ns = "cxxrtl_design";
	std::ostream *impl_f = nullptr;
	std::ostream *intf_f = nullptr;

	bool print_wire_types = false;
	bool print_debug_wire_types = false;
	bool run_hierarchy = false;
	bool run_flatten = false;
	bool run_proc = false;

	bool unbuffer_internal = false;
	bool unbuffer_public = false;
	bool localize_internal = false;
	bool localize_public = false;
	bool inline_internal = false;
	bool inline_public = false;

	bool debug_info = false;
	bool debug_member = false;
	bool debug_alias = false;
	bool debug_eval = false;

	std::ostringstream f;
	std::string indent;
	int temporary = 0;

	dict<const RTLIL::Module*, SigMap> sigmaps;
	pool<const RTLIL::Wire*> edge_wires;
	dict<RTLIL::SigBit, RTLIL::SyncType> edge_types;
	pool<const RTLIL::Memory*> writable_memories;
	dict<const RTLIL::Cell*, pool<const RTLIL::Cell*>> transparent_for;
	dict<const RTLIL::Module*, std::vector<FlowGraph::Node>> schedule, debug_schedule;
	dict<const RTLIL::Wire*, WireType> wire_types, debug_wire_types;
	dict<RTLIL::SigBit, bool> bit_has_state;
	dict<const RTLIL::Module*, pool<std::string>> blackbox_specializations;
	dict<const RTLIL::Module*, bool> eval_converges;

	void inc_indent() {
		indent += "\t";
	}
	void dec_indent() {
		indent.resize(indent.size() - 1);
	}

	// RTLIL allows any characters in names other than whitespace. This presents an issue for generating C++ code
	// because C++ identifiers may be only alphanumeric, cannot clash with C++ keywords, and cannot clash with cxxrtl
	// identifiers. This issue can be solved with a name mangling scheme. We choose a name mangling scheme that results
	// in readable identifiers, does not depend on an up-to-date list of C++ keywords, and is easy to apply. Its rules:
	//  1. All generated identifiers start with `_`.
	//  1a. Generated identifiers for public names (beginning with `\`) start with `p_`.
	//  1b. Generated identifiers for internal names (beginning with `$`) start with `i_`.
	//  2. An underscore is escaped with another underscore, i.e. `__`.
	//  3. Any other non-alnum character is escaped with underscores around its lowercase hex code, e.g. `@` as `_40_`.
	std::string mangle_name(const RTLIL::IdString &name)
	{
		std::string mangled;
		bool first = true;
		for (char c : name.str()) {
			if (first) {
				first = false;
				if (c == '\\')
					mangled += "p_";
				else if (c == '$')
					mangled += "i_";
				else
					log_assert(false);
			} else {
				if (isalnum(c)) {
					mangled += c;
				} else if (c == '_') {
					mangled += "__";
				} else {
					char l = c & 0xf, h = (c >> 4) & 0xf;
					mangled += '_';
					mangled += (h < 10 ? '0' + h : 'a' + h - 10);
					mangled += (l < 10 ? '0' + l : 'a' + l - 10);
					mangled += '_';
				}
			}
		}
		return mangled;
	}

	std::string mangle_module_name(const RTLIL::IdString &name, bool is_blackbox = false)
	{
		// Class namespace.
		if (is_blackbox)
			return "bb_" + mangle_name(name);
		return mangle_name(name);
	}

	std::string mangle_memory_name(const RTLIL::IdString &name)
	{
		// Class member namespace.
		return "memory_" + mangle_name(name);
	}

	std::string mangle_cell_name(const RTLIL::IdString &name)
	{
		// Class member namespace.
		return "cell_" + mangle_name(name);
	}

	std::string mangle_wire_name(const RTLIL::IdString &name)
	{
		// Class member namespace.
		return mangle_name(name);
	}

	std::string mangle(const RTLIL::Module *module)
	{
		return mangle_module_name(module->name, /*is_blackbox=*/module->get_bool_attribute(ID(cxxrtl_blackbox)));
	}

	std::string mangle(const RTLIL::Memory *memory)
	{
		return mangle_memory_name(memory->name);
	}

	std::string mangle(const RTLIL::Cell *cell)
	{
		return mangle_cell_name(cell->name);
	}

	std::string mangle(const RTLIL::Wire *wire)
	{
		return mangle_wire_name(wire->name);
	}

	std::string mangle(RTLIL::SigBit sigbit)
	{
		log_assert(sigbit.wire != NULL);
		if (sigbit.wire->width == 1)
			return mangle(sigbit.wire);
		return mangle(sigbit.wire) + "_" + std::to_string(sigbit.offset);
	}

	std::vector<std::string> template_param_names(const RTLIL::Module *module)
	{
		if (!module->has_attribute(ID(cxxrtl_template)))
			return {};

		if (module->attributes.at(ID(cxxrtl_template)).flags != RTLIL::CONST_FLAG_STRING)
			log_cmd_error("Attribute `cxxrtl_template' of module `%s' is not a string.\n", log_id(module));

		std::vector<std::string> param_names = split_by(module->get_string_attribute(ID(cxxrtl_template)), " \t");
		for (const auto &param_name : param_names) {
			// Various lowercase prefixes (p_, i_, cell_, ...) are used for member variables, so require
			// parameters to start with an uppercase letter to avoid name conflicts. (This is the convention
			// in both Verilog and C++, anyway.)
			if (!isupper(param_name[0]))
				log_cmd_error("Attribute `cxxrtl_template' of module `%s' includes a parameter `%s', "
				              "which does not start with an uppercase letter.\n",
				              log_id(module), param_name.c_str());
		}
		return param_names;
	}

	std::string template_params(const RTLIL::Module *module, bool is_decl)
	{
		std::vector<std::string> param_names = template_param_names(module);
		if (param_names.empty())
			return "";

		std::string params = "<";
		bool first = true;
		for (const auto &param_name : param_names) {
			if (!first)
				params += ", ";
			first = false;
			if (is_decl)
				params += "size_t ";
			params += param_name;
		}
		params += ">";
		return params;
	}

	std::string template_args(const RTLIL::Cell *cell)
	{
		RTLIL::Module *cell_module = cell->module->design->module(cell->type);
		log_assert(cell_module != nullptr);
		if (!cell_module->get_bool_attribute(ID(cxxrtl_blackbox)))
			return "";

		std::vector<std::string> param_names = template_param_names(cell_module);
		if (param_names.empty())
			return "";

		std::string params = "<";
		bool first = true;
		for (const auto &param_name : param_names) {
			if (!first)
				params += ", ";
			first = false;
			params += "/*" + param_name + "=*/";
			RTLIL::IdString id_param_name = '\\' + param_name;
			if (!cell->hasParam(id_param_name))
				log_cmd_error("Cell `%s.%s' does not have a parameter `%s', which is required by the templated module `%s'.\n",
				              log_id(cell->module), log_id(cell), param_name.c_str(), log_id(cell_module));
			RTLIL::Const param_value = cell->getParam(id_param_name);
			if (((param_value.flags & ~RTLIL::CONST_FLAG_SIGNED) != 0) || param_value.as_int() < 0)
				log_cmd_error("Parameter `%s' of cell `%s.%s', which is required by the templated module `%s', "
				              "is not a positive integer.\n",
				              param_name.c_str(), log_id(cell->module), log_id(cell), log_id(cell_module));
			params += std::to_string(cell->getParam(id_param_name).as_int());
		}
		params += ">";
		return params;
	}

	std::string fresh_temporary()
	{
		return stringf("tmp_%d", temporary++);
	}

	void dump_attrs(const RTLIL::AttrObject *object)
	{
		for (auto attr : object->attributes) {
			f << indent << "// " << attr.first.str() << ": ";
			if (attr.second.flags & RTLIL::CONST_FLAG_STRING) {
				f << attr.second.decode_string();
			} else {
				f << attr.second.as_int(/*is_signed=*/attr.second.flags & RTLIL::CONST_FLAG_SIGNED);
			}
			f << "\n";
		}
	}

	void dump_const_init(const RTLIL::Const &data, int width, int offset = 0, bool fixed_width = false)
	{
		const int CHUNK_SIZE = 32;
		f << "{";
		while (width > 0) {
			int chunk_width = min(width, CHUNK_SIZE);
			uint32_t chunk = data.extract(offset, chunk_width).as_int();
			if (fixed_width)
				f << stringf("0x%.*xu", (3 + chunk_width) / 4, chunk);
			else
				f << stringf("%#xu", chunk);
			if (width > CHUNK_SIZE)
				f << ',';
			offset += CHUNK_SIZE;
			width  -= CHUNK_SIZE;
		}
		f << "}";
	}

	void dump_const_init(const RTLIL::Const &data)
	{
		dump_const_init(data, data.size());
	}

	void dump_const(const RTLIL::Const &data, int width, int offset = 0, bool fixed_width = false)
	{
		f << "value<" << width << ">";
		dump_const_init(data, width, offset, fixed_width);
	}

	void dump_const(const RTLIL::Const &data)
	{
		dump_const(data, data.size());
	}

	bool dump_sigchunk(const RTLIL::SigChunk &chunk, bool is_lhs, bool for_debug = false)
	{
		if (chunk.wire == NULL) {
			dump_const(chunk.data, chunk.width, chunk.offset);
			return false;
		} else {
			const auto &wire_type = (for_debug ? debug_wire_types : wire_types)[chunk.wire];
			switch (wire_type.type) {
				case WireType::BUFFERED:
					f << mangle(chunk.wire) << (is_lhs ? ".next" : ".curr");
					break;
				case WireType::MEMBER:
				case WireType::LOCAL:
				case WireType::OUTLINE:
					f << mangle(chunk.wire);
					break;
				case WireType::INLINE:
					log_assert(!is_lhs);
					if (wire_type.cell_subst != nullptr) {
						dump_cell_expr(wire_type.cell_subst, for_debug);
						break;
					}
					YS_FALLTHROUGH
				case WireType::ALIAS:
				case WireType::CONST:
					log_assert(!is_lhs);
					return dump_sigspec(wire_type.sig_subst.extract(chunk.offset, chunk.width), is_lhs, for_debug);
				case WireType::UNUSED:
					log_assert(is_lhs);
					f << "value<" << chunk.width << ">()";
					return false;
			}
			if (chunk.width == chunk.wire->width && chunk.offset == 0)
				return false;
			else if (chunk.width == 1)
				f << ".slice<" << chunk.offset << ">()";
			else
				f << ".slice<" << chunk.offset+chunk.width-1 << "," << chunk.offset << ">()";
			return true;
		}
	}

	bool dump_sigspec(const RTLIL::SigSpec &sig, bool is_lhs, bool for_debug = false)
	{
		if (sig.empty()) {
			f << "value<0>()";
			return false;
		} else if (sig.is_chunk()) {
			return dump_sigchunk(sig.as_chunk(), is_lhs, for_debug);
		} else {
			bool first = true;
			auto chunks = sig.chunks();
			for (auto it = chunks.rbegin(); it != chunks.rend(); it++) {
				if (!first)
					f << ".concat(";
				bool is_complex = dump_sigchunk(*it, is_lhs, for_debug);
				if (!is_lhs && it->width == 1) {
					size_t repeat = 1;
					while ((it + repeat) != chunks.rend() && *(it + repeat) == *it)
						repeat++;
					if (repeat > 1) {
						if (is_complex)
							f << ".val()";
						f << ".repeat<" << repeat << ">()";
					}
					it += repeat - 1;
				}
				if (!first)
					f << ")";
				first = false;
			}
			return true;
		}
	}

	void dump_sigspec_lhs(const RTLIL::SigSpec &sig, bool for_debug = false)
	{
		dump_sigspec(sig, /*is_lhs=*/true, for_debug);
	}

	void dump_sigspec_rhs(const RTLIL::SigSpec &sig, bool for_debug = false)
	{
		// In the contexts where we want template argument deduction to occur for `template<size_t Bits> ... value<Bits>`,
		// it is necessary to have the argument to already be a `value<N>`, since template argument deduction and implicit
		// type conversion are mutually exclusive. In these contexts, we use dump_sigspec_rhs() to emit an explicit
		// type conversion, but only if the expression needs it.
		bool is_complex = dump_sigspec(sig, /*is_lhs=*/false, for_debug);
		if (is_complex)
			f << ".val()";
	}

	void dump_inlined_cells(const std::vector<const RTLIL::Cell*> &cells)
	{
		if (cells.empty()) {
			f << indent << "// connection\n";
		} else if (cells.size() == 1) {
			dump_attrs(cells.front());
			f << indent << "// cell " << cells.front()->name.str() << "\n";
		} else {
			f << indent << "// cells";
			for (auto cell : cells)
				f << " " << cell->name.str();
			f << "\n";
		}
	}

	void collect_sigspec_rhs(const RTLIL::SigSpec &sig, bool for_debug, std::vector<const RTLIL::Cell*> &cells)
	{
		for (auto chunk : sig.chunks()) {
			if (!chunk.wire)
				continue;
			const auto &wire_type = wire_types[chunk.wire];
			switch (wire_type.type) {
				case WireType::INLINE:
					if (wire_type.cell_subst != nullptr) {
						collect_cell_eval(wire_type.cell_subst, for_debug, cells);
						break;
					}
					YS_FALLTHROUGH
				case WireType::ALIAS:
					collect_sigspec_rhs(wire_type.sig_subst, for_debug, cells);
					break;
				default:
					break;
			}
		}
	}

	void dump_connect_expr(const RTLIL::SigSig &conn, bool for_debug = false)
	{
		dump_sigspec_rhs(conn.second, for_debug);
	}

	void dump_connect(const RTLIL::SigSig &conn, bool for_debug = false)
	{
		std::vector<const RTLIL::Cell*> inlined_cells;
		collect_sigspec_rhs(conn.second, for_debug, inlined_cells);
		dump_inlined_cells(inlined_cells);

		f << indent;
		dump_sigspec_lhs(conn.first, for_debug);
		f << " = ";
		dump_connect_expr(conn, for_debug);
		f << ";\n";
	}

	void collect_connect(const RTLIL::SigSig &conn, bool for_debug, std::vector<const RTLIL::Cell*> &cells)
	{
		collect_sigspec_rhs(conn.second, for_debug, cells);
	}

	void dump_cell_sync(const RTLIL::Cell *cell, bool for_debug = false)
	{
		const char *access = is_cxxrtl_blackbox_cell(cell) ? "->" : ".";
		f << indent << "// cell " << cell->name.str() << " syncs\n";
		for (auto conn : cell->connections())
			if (cell->output(conn.first))
				if (is_cxxrtl_sync_port(cell, conn.first)) {
					f << indent;
					dump_sigspec_lhs(conn.second, for_debug);
					f << " = " << mangle(cell) << access << mangle_wire_name(conn.first) << ".curr;\n";
				}
	}

	void dump_cell_expr(const RTLIL::Cell *cell, bool for_debug = false)
	{
		// Unary cells
		if (is_unary_cell(cell->type)) {
			f << cell->type.substr(1);
			if (is_extending_cell(cell->type))
				f << '_' << (cell->getParam(ID::A_SIGNED).as_bool() ? 's' : 'u');
			f << "<" << cell->getParam(ID::Y_WIDTH).as_int() << ">(";
			dump_sigspec_rhs(cell->getPort(ID::A), for_debug);
			f << ")";
		// Binary cells
		} else if (is_binary_cell(cell->type)) {
			f << cell->type.substr(1);
			if (is_extending_cell(cell->type))
				f << '_' << (cell->getParam(ID::A_SIGNED).as_bool() ? 's' : 'u') <<
				            (cell->getParam(ID::B_SIGNED).as_bool() ? 's' : 'u');
			f << "<" << cell->getParam(ID::Y_WIDTH).as_int() << ">(";
			dump_sigspec_rhs(cell->getPort(ID::A), for_debug);
			f << ", ";
			dump_sigspec_rhs(cell->getPort(ID::B), for_debug);
			f << ")";
		// Muxes
		} else if (cell->type == ID($mux)) {
			f << "(";
			dump_sigspec_rhs(cell->getPort(ID::S), for_debug);
			f << " ? ";
			dump_sigspec_rhs(cell->getPort(ID::B), for_debug);
			f << " : ";
			dump_sigspec_rhs(cell->getPort(ID::A), for_debug);
			f << ")";
		// Parallel (one-hot) muxes
		} else if (cell->type == ID($pmux)) {
			int width = cell->getParam(ID::WIDTH).as_int();
			int s_width = cell->getParam(ID::S_WIDTH).as_int();
			for (int part = 0; part < s_width; part++) {
				f << "(";
				dump_sigspec_rhs(cell->getPort(ID::S).extract(part), for_debug);
				f << " ? ";
				dump_sigspec_rhs(cell->getPort(ID::B).extract(part * width, width), for_debug);
				f << " : ";
			}
			dump_sigspec_rhs(cell->getPort(ID::A), for_debug);
			for (int part = 0; part < s_width; part++) {
				f << ")";
			}
		// Concats
		} else if (cell->type == ID($concat)) {
			dump_sigspec_rhs(cell->getPort(ID::B), for_debug);
			f << ".concat(";
			dump_sigspec_rhs(cell->getPort(ID::A), for_debug);
			f << ").val()";
		// Slices
		} else if (cell->type == ID($slice)) {
			dump_sigspec_rhs(cell->getPort(ID::A), for_debug);
			f << ".slice<";
			f << cell->getParam(ID::OFFSET).as_int() + cell->getParam(ID::Y_WIDTH).as_int() - 1;
			f << ",";
			f << cell->getParam(ID::OFFSET).as_int();
			f << ">().val()";
		} else {
			log_assert(false);
		}
	}

	void dump_cell_eval(const RTLIL::Cell *cell, bool for_debug = false)
	{
		std::vector<const RTLIL::Cell*> inlined_cells;
		collect_cell_eval(cell, for_debug, inlined_cells);
		dump_inlined_cells(inlined_cells);

		// Elidable cells
		if (is_inlinable_cell(cell->type)) {
			f << indent;
			dump_sigspec_lhs(cell->getPort(ID::Y), for_debug);
			f << " = ";
			dump_cell_expr(cell, for_debug);
			f << ";\n";
		// Flip-flops
		} else if (is_ff_cell(cell->type)) {
			log_assert(!for_debug);
			// Clocks might be slices of larger signals but should only ever be single bit
			if (cell->hasPort(ID::CLK) && is_valid_clock(cell->getPort(ID::CLK))) {
				// Edge-sensitive logic
				RTLIL::SigBit clk_bit = cell->getPort(ID::CLK)[0];
				clk_bit = sigmaps[clk_bit.wire->module](clk_bit);
				if (clk_bit.wire) {
					f << indent << "if (" << (cell->getParam(ID::CLK_POLARITY).as_bool() ? "posedge_" : "negedge_")
					            << mangle(clk_bit) << ") {\n";
				} else {
					f << indent << "if (false) {\n";
				}
				inc_indent();
					if (cell->hasPort(ID::EN)) {
						f << indent << "if (";
						dump_sigspec_rhs(cell->getPort(ID::EN));
						f << " == value<1> {" << cell->getParam(ID::EN_POLARITY).as_bool() << "u}) {\n";
						inc_indent();
					}
					f << indent;
					dump_sigspec_lhs(cell->getPort(ID::Q));
					f << " = ";
					dump_sigspec_rhs(cell->getPort(ID::D));
					f << ";\n";
					if (cell->hasPort(ID::EN) && cell->type != ID($sdffce)) {
						dec_indent();
						f << indent << "}\n";
					}
					if (cell->hasPort(ID::SRST)) {
						f << indent << "if (";
						dump_sigspec_rhs(cell->getPort(ID::SRST));
						f << " == value<1> {" << cell->getParam(ID::SRST_POLARITY).as_bool() << "u}) {\n";
						inc_indent();
							f << indent;
							dump_sigspec_lhs(cell->getPort(ID::Q));
							f << " = ";
							dump_const(cell->getParam(ID::SRST_VALUE));
							f << ";\n";
						dec_indent();
						f << indent << "}\n";
					}
					if (cell->hasPort(ID::EN) && cell->type == ID($sdffce)) {
						dec_indent();
						f << indent << "}\n";
					}
				dec_indent();
				f << indent << "}\n";
			} else if (cell->hasPort(ID::EN)) {
				// Level-sensitive logic
				f << indent << "if (";
				dump_sigspec_rhs(cell->getPort(ID::EN));
				f << " == value<1> {" << cell->getParam(ID::EN_POLARITY).as_bool() << "u}) {\n";
				inc_indent();
					f << indent;
					dump_sigspec_lhs(cell->getPort(ID::Q));
					f << " = ";
					dump_sigspec_rhs(cell->getPort(ID::D));
					f << ";\n";
				dec_indent();
				f << indent << "}\n";
			}
			if (cell->hasPort(ID::ARST)) {
				// Asynchronous reset (entire coarse cell at once)
				f << indent << "if (";
				dump_sigspec_rhs(cell->getPort(ID::ARST));
				f << " == value<1> {" << cell->getParam(ID::ARST_POLARITY).as_bool() << "u}) {\n";
				inc_indent();
					f << indent;
					dump_sigspec_lhs(cell->getPort(ID::Q));
					f << " = ";
					dump_const(cell->getParam(ID::ARST_VALUE));
					f << ";\n";
				dec_indent();
				f << indent << "}\n";
			}
			if (cell->hasPort(ID::SET)) {
				// Asynchronous set (for individual bits)
				f << indent;
				dump_sigspec_lhs(cell->getPort(ID::Q));
				f << " = ";
				dump_sigspec_lhs(cell->getPort(ID::Q));
				f << ".update(";
				dump_const(RTLIL::Const(RTLIL::S1, cell->getParam(ID::WIDTH).as_int()));
				f << ", ";
				dump_sigspec_rhs(cell->getPort(ID::SET));
				f << (cell->getParam(ID::SET_POLARITY).as_bool() ? "" : ".bit_not()") << ");\n";
			}
			if (cell->hasPort(ID::CLR)) {
				// Asynchronous clear (for individual bits; priority over set)
				f << indent;
				dump_sigspec_lhs(cell->getPort(ID::Q));
				f << " = ";
				dump_sigspec_lhs(cell->getPort(ID::Q));
				f << ".update(";
				dump_const(RTLIL::Const(RTLIL::S0, cell->getParam(ID::WIDTH).as_int()));
				f << ", ";
				dump_sigspec_rhs(cell->getPort(ID::CLR));
				f << (cell->getParam(ID::CLR_POLARITY).as_bool() ? "" : ".bit_not()") << ");\n";
			}
		// Memory ports
		} else if (cell->type.in(ID($memrd), ID($memwr))) {
			if (cell->getParam(ID::CLK_ENABLE).as_bool()) {
				log_assert(!for_debug);
				RTLIL::SigBit clk_bit = cell->getPort(ID::CLK)[0];
				clk_bit = sigmaps[clk_bit.wire->module](clk_bit);
				if (clk_bit.wire) {
					f << indent << "if (" << (cell->getParam(ID::CLK_POLARITY).as_bool() ? "posedge_" : "negedge_")
					            << mangle(clk_bit) << ") {\n";
				} else {
					f << indent << "if (false) {\n";
				}
				inc_indent();
			}
			RTLIL::Memory *memory = cell->module->memories[cell->getParam(ID::MEMID).decode_string()];
			std::string valid_index_temp = fresh_temporary();
			f << indent << "auto " << valid_index_temp << " = memory_index(";
			// Almost all non-elidable cells cannot appear in debug_eval(), but $memrd is an exception; asynchronous
			// memory read ports can.
			dump_sigspec_rhs(cell->getPort(ID::ADDR), for_debug);
			f << ", " << memory->start_offset << ", " << memory->size << ");\n";
			if (cell->type == ID($memrd)) {
				bool has_enable = cell->getParam(ID::CLK_ENABLE).as_bool() && !cell->getPort(ID::EN).is_fully_ones();
				if (has_enable) {
					f << indent << "if (";
					dump_sigspec_rhs(cell->getPort(ID::EN));
					f << ") {\n";
					inc_indent();
				}
				// The generated code has two bounds checks; one in an assertion, and another that guards the read.
				// This is done so that the code does not invoke undefined behavior under any conditions, but nevertheless
				// loudly crashes if an illegal condition is encountered. The assert may be turned off with -DCXXRTL_NDEBUG
				// not only for release builds, but also to make sure the simulator (which is presumably embedded in some
				// larger program) will never crash the code that calls into it.
				//
				// If assertions are disabled, out of bounds reads are defined to return zero.
				f << indent << "CXXRTL_ASSERT(" << valid_index_temp << ".valid && \"out of bounds read\");\n";
				f << indent << "if(" << valid_index_temp << ".valid) {\n";
				inc_indent();
					if (writable_memories[memory]) {
						std::string lhs_temp = fresh_temporary();
						f << indent << "value<" << memory->width << "> " << lhs_temp << " = "
						            << mangle(memory) << "[" << valid_index_temp << ".index];\n";
						std::vector<const RTLIL::Cell*> memwr_cells(transparent_for[cell].begin(), transparent_for[cell].end());
						if (!memwr_cells.empty()) {
							std::string addr_temp = fresh_temporary();
							f << indent << "const value<" << cell->getPort(ID::ADDR).size() << "> &" << addr_temp << " = ";
							dump_sigspec_rhs(cell->getPort(ID::ADDR));
							f << ";\n";
							std::sort(memwr_cells.begin(), memwr_cells.end(),
								[](const RTLIL::Cell *a, const RTLIL::Cell *b) {
									return a->getParam(ID::PRIORITY).as_int() < b->getParam(ID::PRIORITY).as_int();
								});
							for (auto memwr_cell : memwr_cells) {
								f << indent << "if (" << addr_temp << " == ";
								dump_sigspec_rhs(memwr_cell->getPort(ID::ADDR));
								f << ") {\n";
								inc_indent();
									f << indent << lhs_temp << " = " << lhs_temp;
									f << ".update(";
									dump_sigspec_rhs(memwr_cell->getPort(ID::DATA));
									f << ", ";
									dump_sigspec_rhs(memwr_cell->getPort(ID::EN));
									f << ");\n";
								dec_indent();
								f << indent << "}\n";
							}
						}
						f << indent;
						dump_sigspec_lhs(cell->getPort(ID::DATA));
						f << " = " << lhs_temp << ";\n";
					} else {
						f << indent;
						dump_sigspec_lhs(cell->getPort(ID::DATA));
						f << " = " << mangle(memory) << "[" << valid_index_temp << ".index];\n";
					}
				dec_indent();
				f << indent << "} else {\n";
				inc_indent();
					f << indent;
					dump_sigspec_lhs(cell->getPort(ID::DATA));
					f << " = value<" << memory->width << "> {};\n";
				dec_indent();
				f << indent << "}\n";
				if (has_enable) {
					dec_indent();
					f << indent << "}\n";
				}
			} else /*if (cell->type == ID($memwr))*/ {
				log_assert(writable_memories[memory]);
				// See above for rationale of having both the assert and the condition.
				//
				// If assertions are disabled, out of bounds writes are defined to do nothing.
				f << indent << "CXXRTL_ASSERT(" << valid_index_temp << ".valid && \"out of bounds write\");\n";
				f << indent << "if (" << valid_index_temp << ".valid) {\n";
				inc_indent();
					f << indent << mangle(memory) << ".update(" << valid_index_temp << ".index, ";
					dump_sigspec_rhs(cell->getPort(ID::DATA));
					f << ", ";
					dump_sigspec_rhs(cell->getPort(ID::EN));
					f << ", " << cell->getParam(ID::PRIORITY).as_int() << ");\n";
				dec_indent();
				f << indent << "}\n";
			}
			if (cell->getParam(ID::CLK_ENABLE).as_bool()) {
				dec_indent();
				f << indent << "}\n";
			}
		// Internal cells
		} else if (is_internal_cell(cell->type)) {
			log_cmd_error("Unsupported internal cell `%s'.\n", cell->type.c_str());
		// User cells
		} else {
			log_assert(!for_debug);
			log_assert(cell->known());
			bool buffered_inputs = false;
			const char *access = is_cxxrtl_blackbox_cell(cell) ? "->" : ".";
			for (auto conn : cell->connections())
				if (cell->input(conn.first)) {
					RTLIL::Module *cell_module = cell->module->design->module(cell->type);
					log_assert(cell_module != nullptr && cell_module->wire(conn.first) && conn.second.is_wire());
					RTLIL::Wire *cell_module_wire = cell_module->wire(conn.first);
					f << indent << mangle(cell) << access << mangle_wire_name(conn.first);
					if (!is_cxxrtl_blackbox_cell(cell) && wire_types[cell_module_wire].is_buffered()) {
						buffered_inputs = true;
						f << ".next";
					}
					f << " = ";
					dump_sigspec_rhs(conn.second);
					f << ";\n";
					if (getenv("CXXRTL_VOID_MY_WARRANTY")) {
						// Until we have proper clock tree detection, this really awful hack that opportunistically
						// propagates prev_* values for clocks can be used to estimate how much faster a design could
						// be if only one clock edge was simulated by replacing:
						//   top.p_clk = value<1>{0u}; top.step();
						//   top.p_clk = value<1>{1u}; top.step();
						// with:
						//   top.prev_p_clk = value<1>{0u}; top.p_clk = value<1>{1u}; top.step();
						// Don't rely on this; it will be removed without warning.
						if (edge_wires[conn.second.as_wire()] && edge_wires[cell_module_wire]) {
							f << indent << mangle(cell) << access << "prev_" << mangle(cell_module_wire) << " = ";
							f << "prev_" << mangle(conn.second.as_wire()) << ";\n";
						}
					}
				}
			auto assign_from_outputs = [&](bool cell_converged) {
				for (auto conn : cell->connections()) {
					if (cell->output(conn.first)) {
						if (conn.second.empty())
							continue; // ignore disconnected ports
						if (is_cxxrtl_sync_port(cell, conn.first))
							continue; // fully sync ports are handled in CELL_SYNC nodes
						f << indent;
						dump_sigspec_lhs(conn.second);
						f << " = " << mangle(cell) << access << mangle_wire_name(conn.first);
						// Similarly to how there is no purpose to buffering cell inputs, there is also no purpose to buffering
						// combinatorial cell outputs in case the cell converges within one cycle. (To convince yourself that
						// this optimization is valid, consider that, since the cell converged within one cycle, it would not
						// have any buffered wires if they were not output ports. Imagine inlining the cell's eval() function,
						// and consider the fate of the localized wires that used to be output ports.)
						//
						// It is not possible to know apriori whether the cell (which may be late bound) will converge immediately.
						// Because of this, the choice between using .curr (appropriate for buffered outputs) and .next (appropriate
						// for unbuffered outputs) is made at runtime.
						if (cell_converged && is_cxxrtl_comb_port(cell, conn.first))
							f << ".next;\n";
						else
							f << ".curr;\n";
					}
				}
			};
			if (buffered_inputs) {
				// If we have any buffered inputs, there's no chance of converging immediately.
				f << indent << mangle(cell) << access << "eval();\n";
				f << indent << "converged = false;\n";
				assign_from_outputs(/*cell_converged=*/false);
			} else {
				f << indent << "if (" << mangle(cell) << access << "eval()) {\n";
				inc_indent();
					assign_from_outputs(/*cell_converged=*/true);
				dec_indent();
				f << indent << "} else {\n";
				inc_indent();
					f << indent << "converged = false;\n";
					assign_from_outputs(/*cell_converged=*/false);
				dec_indent();
				f << indent << "}\n";
			}
		}
	}

	void collect_cell_eval(const RTLIL::Cell *cell, bool for_debug, std::vector<const RTLIL::Cell*> &cells)
	{
		cells.push_back(cell);
		for (auto port : cell->connections())
			if (cell->input(port.first))
				collect_sigspec_rhs(port.second, for_debug, cells);
	}

	void dump_assign(const RTLIL::SigSig &sigsig, bool for_debug = false)
	{
		f << indent;
		dump_sigspec_lhs(sigsig.first, for_debug);
		f << " = ";
		dump_sigspec_rhs(sigsig.second, for_debug);
		f << ";\n";
	}

	void dump_case_rule(const RTLIL::CaseRule *rule, bool for_debug = false)
	{
		for (auto action : rule->actions)
			dump_assign(action, for_debug);
		for (auto switch_ : rule->switches)
			dump_switch_rule(switch_, for_debug);
	}

	void dump_switch_rule(const RTLIL::SwitchRule *rule, bool for_debug = false)
	{
		// The switch attributes are printed before the switch condition is captured.
		dump_attrs(rule);
		std::string signal_temp = fresh_temporary();
		f << indent << "const value<" << rule->signal.size() << "> &" << signal_temp << " = ";
		dump_sigspec(rule->signal, /*is_lhs=*/false, for_debug);
		f << ";\n";

		bool first = true;
		for (auto case_ : rule->cases) {
			// The case attributes (for nested cases) are printed before the if/else if/else statement.
			dump_attrs(rule);
			f << indent;
			if (!first)
				f << "} else ";
			first = false;
			if (!case_->compare.empty()) {
				f << "if (";
				bool first = true;
				for (auto &compare : case_->compare) {
					if (!first)
						f << " || ";
					first = false;
					if (compare.is_fully_def()) {
						f << signal_temp << " == ";
						dump_sigspec(compare, /*is_lhs=*/false, for_debug);
					} else if (compare.is_fully_const()) {
						RTLIL::Const compare_mask, compare_value;
						for (auto bit : compare.as_const()) {
							switch (bit) {
								case RTLIL::S0:
								case RTLIL::S1:
									compare_mask.bits.push_back(RTLIL::S1);
									compare_value.bits.push_back(bit);
									break;

								case RTLIL::Sx:
								case RTLIL::Sz:
								case RTLIL::Sa:
									compare_mask.bits.push_back(RTLIL::S0);
									compare_value.bits.push_back(RTLIL::S0);
									break;

								default:
									log_assert(false);
							}
						}
						f << "and_uu<" << compare.size() << ">(" << signal_temp << ", ";
						dump_const(compare_mask);
						f << ") == ";
						dump_const(compare_value);
					} else {
						log_assert(false);
					}
				}
				f << ") ";
			}
			f << "{\n";
			inc_indent();
				dump_case_rule(case_, for_debug);
			dec_indent();
		}
		f << indent << "}\n";
	}

	void dump_process_case(const RTLIL::Process *proc, bool for_debug = false)
	{
		dump_attrs(proc);
		f << indent << "// process " << proc->name.str() << " case\n";
		// The case attributes (for root case) are always empty.
		log_assert(proc->root_case.attributes.empty());
		dump_case_rule(&proc->root_case, for_debug);
	}

	void dump_process_syncs(const RTLIL::Process *proc, bool for_debug = false)
	{
		dump_attrs(proc);
		f << indent << "// process " << proc->name.str() << " syncs\n";
		for (auto sync : proc->syncs) {
			log_assert(!for_debug || sync->type == RTLIL::STa);

			RTLIL::SigBit sync_bit;
			if (!sync->signal.empty()) {
				sync_bit = sync->signal[0];
				sync_bit = sigmaps[sync_bit.wire->module](sync_bit);
				if (!sync_bit.is_wire())
					continue; // a clock, or more commonly a reset, can be tied to a constant driver
			}

			pool<std::string> events;
			switch (sync->type) {
				case RTLIL::STp:
					log_assert(sync_bit.wire != nullptr);
					events.insert("posedge_" + mangle(sync_bit));
					break;
				case RTLIL::STn:
					log_assert(sync_bit.wire != nullptr);
					events.insert("negedge_" + mangle(sync_bit));
					break;
				case RTLIL::STe:
					log_assert(sync_bit.wire != nullptr);
					events.insert("posedge_" + mangle(sync_bit));
					events.insert("negedge_" + mangle(sync_bit));
					break;

				case RTLIL::STa:
					events.insert("true");
					break;

				case RTLIL::ST0:
				case RTLIL::ST1:
				case RTLIL::STg:
				case RTLIL::STi:
					log_assert(false);
			}
			if (!events.empty()) {
				f << indent << "if (";
				bool first = true;
				for (auto &event : events) {
					if (!first)
						f << " || ";
					first = false;
					f << event;
				}
				f << ") {\n";
				inc_indent();
					for (auto action : sync->actions)
						dump_assign(action, for_debug);
				dec_indent();
				f << indent << "}\n";
			}
		}
	}

	void dump_wire(const RTLIL::Wire *wire, bool is_local)
	{
		const auto &wire_type = wire_types[wire];
		if (!wire_type.is_named() || wire_type.is_local() != is_local)
			return;

		dump_attrs(wire);
		f << indent;
		if (wire->port_input && wire->port_output)
			f << "/*inout*/ ";
		else if (wire->port_input)
			f << "/*input*/ ";
		else if (wire->port_output)
			f << "/*output*/ ";
		f << (wire_type.is_buffered() ? "wire" : "value");
		if (wire->module->has_attribute(ID(cxxrtl_blackbox)) && wire->has_attribute(ID(cxxrtl_width))) {
			f << "<" << wire->get_string_attribute(ID(cxxrtl_width)) << ">";
		} else {
			f << "<" << wire->width << ">";
		}
		f << " " << mangle(wire);
		if (wire->has_attribute(ID::init)) {
			f << " ";
			dump_const_init(wire->attributes.at(ID::init));
		}
		f << ";\n";
		if (edge_wires[wire]) {
			if (!wire_type.is_buffered()) {
				f << indent << "value<" << wire->width << "> prev_" << mangle(wire);
				if (wire->has_attribute(ID::init)) {
					f << " ";
					dump_const_init(wire->attributes.at(ID::init));
				}
				f << ";\n";
			}
			for (auto edge_type : edge_types) {
				if (edge_type.first.wire == wire) {
					std::string prev, next;
					if (!wire_type.is_buffered()) {
						prev = "prev_" + mangle(edge_type.first.wire);
						next =           mangle(edge_type.first.wire);
					} else {
						prev = mangle(edge_type.first.wire) + ".curr";
						next = mangle(edge_type.first.wire) + ".next";
					}
					prev += ".slice<" + std::to_string(edge_type.first.offset) + ">().val()";
					next += ".slice<" + std::to_string(edge_type.first.offset) + ">().val()";
					if (edge_type.second != RTLIL::STn) {
						f << indent << "bool posedge_" << mangle(edge_type.first) << "() const {\n";
						inc_indent();
							f << indent << "return !" << prev << " && " << next << ";\n";
						dec_indent();
						f << indent << "}\n";
					}
					if (edge_type.second != RTLIL::STp) {
						f << indent << "bool negedge_" << mangle(edge_type.first) << "() const {\n";
						inc_indent();
							f << indent << "return " << prev << " && !" << next << ";\n";
						dec_indent();
						f << indent << "}\n";
					}
				}
			}
		}
	}

	void dump_debug_wire(const RTLIL::Wire *wire, bool is_local)
	{
		const auto &wire_type = wire_types[wire];
		if (wire_type.is_member())
			return;

		const auto &debug_wire_type = debug_wire_types[wire];
		if (!debug_wire_type.is_named() || debug_wire_type.is_local() != is_local)
			return;

		dump_attrs(wire);
		f << indent;
		if (debug_wire_type.is_outline())
			f << "/*outline*/ ";
		f << "value<" << wire->width << "> " << mangle(wire) << ";\n";
	}

	void dump_memory(RTLIL::Module *module, const RTLIL::Memory *memory)
	{
		vector<const RTLIL::Cell*> init_cells;
		for (auto cell : module->cells())
			if (cell->type == ID($meminit) && cell->getParam(ID::MEMID).decode_string() == memory->name.str())
				init_cells.push_back(cell);

		std::sort(init_cells.begin(), init_cells.end(), [](const RTLIL::Cell *a, const RTLIL::Cell *b) {
			int a_addr = a->getPort(ID::ADDR).as_int(), b_addr = b->getPort(ID::ADDR).as_int();
			int a_prio = a->getParam(ID::PRIORITY).as_int(), b_prio = b->getParam(ID::PRIORITY).as_int();
			return a_prio > b_prio || (a_prio == b_prio && a_addr < b_addr);
		});

		dump_attrs(memory);
		f << indent << "memory<" << memory->width << "> " << mangle(memory)
		            << " { " << memory->size << "u";
		if (init_cells.empty()) {
			f << " };\n";
		} else {
			f << ",\n";
			inc_indent();
				for (auto cell : init_cells) {
					dump_attrs(cell);
					RTLIL::Const data = cell->getPort(ID::DATA).as_const();
					size_t width = cell->getParam(ID::WIDTH).as_int();
					size_t words = cell->getParam(ID::WORDS).as_int();
					f << indent << "memory<" << memory->width << ">::init<" << words << "> { "
					            << stringf("%#x", cell->getPort(ID::ADDR).as_int()) << ", {";
					inc_indent();
						for (size_t n = 0; n < words; n++) {
							if (n % 4 == 0)
								f << "\n" << indent;
							else
								f << " ";
							dump_const(data, width, n * width, /*fixed_width=*/true);
							f << ",";
						}
					dec_indent();
					f << "\n" << indent << "}},\n";
				}
			dec_indent();
			f << indent << "};\n";
		}
	}

	void dump_eval_method(RTLIL::Module *module)
	{
		inc_indent();
			f << indent << "bool converged = " << (eval_converges.at(module) ? "true" : "false") << ";\n";
			if (!module->get_bool_attribute(ID(cxxrtl_blackbox))) {
				for (auto wire : module->wires()) {
					if (edge_wires[wire]) {
						for (auto edge_type : edge_types) {
							if (edge_type.first.wire == wire) {
								if (edge_type.second != RTLIL::STn) {
									f << indent << "bool posedge_" << mangle(edge_type.first) << " = ";
									f << "this->posedge_" << mangle(edge_type.first) << "();\n";
								}
								if (edge_type.second != RTLIL::STp) {
									f << indent << "bool negedge_" << mangle(edge_type.first) << " = ";
									f << "this->negedge_" << mangle(edge_type.first) << "();\n";
								}
							}
						}
					}
				}
				for (auto wire : module->wires())
					dump_wire(wire, /*is_local=*/true);
				for (auto node : schedule[module]) {
					switch (node.type) {
						case FlowGraph::Node::Type::CONNECT:
							dump_connect(node.connect);
							break;
						case FlowGraph::Node::Type::CELL_SYNC:
							dump_cell_sync(node.cell);
							break;
						case FlowGraph::Node::Type::CELL_EVAL:
							dump_cell_eval(node.cell);
							break;
						case FlowGraph::Node::Type::PROCESS_CASE:
							dump_process_case(node.process);
							break;
						case FlowGraph::Node::Type::PROCESS_SYNC:
							dump_process_syncs(node.process);
							break;
					}
				}
			}
			f << indent << "return converged;\n";
		dec_indent();
	}

	void dump_debug_eval_method(RTLIL::Module *module)
	{
		inc_indent();
			for (auto wire : module->wires())
				dump_debug_wire(wire, /*is_local=*/true);
			for (auto node : debug_schedule[module]) {
				switch (node.type) {
					case FlowGraph::Node::Type::CONNECT:
						dump_connect(node.connect, /*for_debug=*/true);
						break;
					case FlowGraph::Node::Type::CELL_SYNC:
						dump_cell_sync(node.cell, /*for_debug=*/true);
						break;
					case FlowGraph::Node::Type::CELL_EVAL:
						dump_cell_eval(node.cell, /*for_debug=*/true);
						break;
					case FlowGraph::Node::Type::PROCESS_CASE:
						dump_process_case(node.process, /*for_debug=*/true);
						break;
					case FlowGraph::Node::Type::PROCESS_SYNC:
						dump_process_syncs(node.process, /*for_debug=*/true);
						break;
					default:
						log_abort();
				}
			}
		dec_indent();
	}

	void dump_commit_method(RTLIL::Module *module)
	{
		inc_indent();
			f << indent << "bool changed = false;\n";
			for (auto wire : module->wires()) {
				const auto &wire_type = wire_types[wire];
				if (wire_type.type == WireType::MEMBER && edge_wires[wire])
					f << indent << "prev_" << mangle(wire) << " = " << mangle(wire) << ";\n";
				if (wire_type.is_buffered())
					f << indent << "if (" << mangle(wire) << ".commit()) changed = true;\n";
			}
			if (!module->get_bool_attribute(ID(cxxrtl_blackbox))) {
				for (auto memory : module->memories) {
					if (!writable_memories[memory.second])
						continue;
					f << indent << "if (" << mangle(memory.second) << ".commit()) changed = true;\n";
				}
				for (auto cell : module->cells()) {
					if (is_internal_cell(cell->type))
						continue;
					const char *access = is_cxxrtl_blackbox_cell(cell) ? "->" : ".";
					f << indent << "if (" << mangle(cell) << access << "commit()) changed = true;\n";
				}
			}
			f << indent << "return changed;\n";
		dec_indent();
	}

	void dump_debug_info_method(RTLIL::Module *module)
	{
		size_t count_public_wires = 0;
		size_t count_member_wires = 0;
		size_t count_undriven = 0;
		size_t count_driven_sync = 0;
		size_t count_driven_comb = 0;
		size_t count_mixed_driver = 0;
		size_t count_alias_wires = 0;
		size_t count_const_wires = 0;
		size_t count_inline_wires = 0;
		size_t count_skipped_wires = 0;
		inc_indent();
			f << indent << "assert(path.empty() || path[path.size() - 1] == ' ');\n";
			for (auto wire : module->wires()) {
				const auto &debug_wire_type = debug_wire_types[wire];
				if (!wire->name.isPublic())
					continue;
				count_public_wires++;
				switch (debug_wire_type.type) {
					case WireType::BUFFERED:
					case WireType::MEMBER: {
						// Member wire
						std::vector<std::string> flags;

						if (wire->port_input && wire->port_output)
							flags.push_back("INOUT");
						else if (wire->port_output)
							flags.push_back("OUTPUT");
						else if (wire->port_input)
							flags.push_back("INPUT");

						bool has_driven_sync = false;
						bool has_driven_comb = false;
						bool has_undriven = false;
						if (!module->get_bool_attribute(ID(cxxrtl_blackbox))) {
							for (auto bit : SigSpec(wire))
								if (!bit_has_state.count(bit))
									has_undriven = true;
								else if (bit_has_state[bit])
									has_driven_sync = true;
								else
									has_driven_comb = true;
						} else if (wire->port_output) {
							switch (cxxrtl_port_type(module, wire->name)) {
								case CxxrtlPortType::SYNC:
									has_driven_sync = true;
									break;
								case CxxrtlPortType::COMB:
									has_driven_comb = true;
									break;
								case CxxrtlPortType::UNKNOWN:
									has_driven_sync = has_driven_comb = true;
									break;
							}
						} else {
							has_undriven = true;
						}
						if (has_undriven)
							flags.push_back("UNDRIVEN");
						if (!has_driven_sync && !has_driven_comb && has_undriven)
							count_undriven++;
						if (has_driven_sync)
							flags.push_back("DRIVEN_SYNC");
						if (has_driven_sync && !has_driven_comb && !has_undriven)
							count_driven_sync++;
						if (has_driven_comb)
							flags.push_back("DRIVEN_COMB");
						if (!has_driven_sync && has_driven_comb && !has_undriven)
							count_driven_comb++;
						if (has_driven_sync + has_driven_comb + has_undriven > 1)
							count_mixed_driver++;

						f << indent << "items.add(path + " << escape_cxx_string(get_hdl_name(wire));
						f << ", debug_item(" << mangle(wire) << ", " << wire->start_offset;
						bool first = true;
						for (auto flag : flags) {
							if (first) {
								first = false;
								f << ", ";
							} else {
								f << "|";
							}
							f << "debug_item::" << flag;
						}
						f << "));\n";
						count_member_wires++;
						break;
					}
					case WireType::ALIAS: {
						// Alias of a member wire
						const RTLIL::Wire *aliasee = debug_wire_type.sig_subst.as_wire();
						f << indent << "items.add(path + " << escape_cxx_string(get_hdl_name(wire));
						f << ", debug_item(";
						// If the aliasee is an outline, then the alias must be an outline, too; otherwise downstream
						// tooling has no way to find out about the outline.
						if (debug_wire_types[aliasee].is_outline())
							f << "debug_eval_outline";
						else
							f << "debug_alias()";
						f << ", " << mangle(aliasee) << ", " << wire->start_offset << "));\n";
						count_alias_wires++;
						break;
					}
					case WireType::CONST: {
						// Wire tied to a constant
						f << indent << "static const value<" << wire->width << "> const_" << mangle(wire) << " = ";
						dump_const(debug_wire_type.sig_subst.as_const());
						f << ";\n";
						f << indent << "items.add(path + " << escape_cxx_string(get_hdl_name(wire));
						f << ", debug_item(const_" << mangle(wire) << ", " << wire->start_offset << "));\n";
						count_const_wires++;
						break;
					}
					case WireType::OUTLINE: {
						// Localized or inlined, but rematerializable wire
						f << indent << "items.add(path + " << escape_cxx_string(get_hdl_name(wire));
						f << ", debug_item(debug_eval_outline, " << mangle(wire) << ", " << wire->start_offset << "));\n";
						count_inline_wires++;
						break;
					}
					default: {
						// Localized or inlined wire with no debug information
						count_skipped_wires++;
						break;
					}
				}
			}
			if (!module->get_bool_attribute(ID(cxxrtl_blackbox))) {
				for (auto &memory_it : module->memories) {
					if (!memory_it.first.isPublic())
						continue;
					f << indent << "items.add(path + " << escape_cxx_string(get_hdl_name(memory_it.second));
					f << ", debug_item(" << mangle(memory_it.second) << ", ";
					f << memory_it.second->start_offset << "));\n";
				}
				for (auto cell : module->cells()) {
					if (is_internal_cell(cell->type))
						continue;
					const char *access = is_cxxrtl_blackbox_cell(cell) ? "->" : ".";
					f << indent << mangle(cell) << access << "debug_info(items, ";
					f << "path + " << escape_cxx_string(get_hdl_name(cell) + ' ') << ");\n";
				}
			}
		dec_indent();

		log_debug("Debug information statistics for module `%s':\n", log_id(module));
		log_debug("  Public wires: %zu, of which:\n", count_public_wires);
		log_debug("    Member wires: %zu, of which:\n", count_member_wires);
		log_debug("      Undriven:     %zu (incl. inputs)\n", count_undriven);
		log_debug("      Driven sync:  %zu\n", count_driven_sync);
		log_debug("      Driven comb:  %zu\n", count_driven_comb);
		log_debug("      Mixed driver: %zu\n", count_mixed_driver);
		if (!module->get_bool_attribute(ID(cxxrtl_blackbox))) {
			log_debug("    Inline wires:   %zu\n", count_inline_wires);
			log_debug("    Alias wires:    %zu\n", count_alias_wires);
			log_debug("    Const wires:    %zu\n", count_const_wires);
			log_debug("    Other wires:    %zu%s\n", count_skipped_wires,
			          count_skipped_wires > 0 ? " (debug unavailable)" : "");
		}
	}

	void dump_metadata_map(const dict<RTLIL::IdString, RTLIL::Const> &metadata_map)
	{
		if (metadata_map.empty()) {
			f << "metadata_map()";
			return;
		}
		f << "metadata_map({\n";
		inc_indent();
			for (auto metadata_item : metadata_map) {
				if (!metadata_item.first.begins_with("\\"))
					continue;
				f << indent << "{ " << escape_cxx_string(metadata_item.first.str().substr(1)) << ", ";
				if (metadata_item.second.flags & RTLIL::CONST_FLAG_REAL) {
					f << std::showpoint << std::stod(metadata_item.second.decode_string()) << std::noshowpoint;
				} else if (metadata_item.second.flags & RTLIL::CONST_FLAG_STRING) {
					f << escape_cxx_string(metadata_item.second.decode_string());
				} else {
					f << metadata_item.second.as_int(/*is_signed=*/metadata_item.second.flags & RTLIL::CONST_FLAG_SIGNED);
					if (!(metadata_item.second.flags & RTLIL::CONST_FLAG_SIGNED))
						f << "u";
				}
				f << " },\n";
			}
		dec_indent();
		f << indent << "})";
	}

	void dump_module_intf(RTLIL::Module *module)
	{
		dump_attrs(module);
		if (module->get_bool_attribute(ID(cxxrtl_blackbox))) {
			if (module->has_attribute(ID(cxxrtl_template)))
				f << indent << "template" << template_params(module, /*is_decl=*/true) << "\n";
			f << indent << "struct " << mangle(module) << " : public module {\n";
			inc_indent();
				for (auto wire : module->wires()) {
					if (wire->port_id != 0)
						dump_wire(wire, /*is_local=*/false);
				}
				f << "\n";
				f << indent << "bool eval() override {\n";
				dump_eval_method(module);
				f << indent << "}\n";
				f << "\n";
				f << indent << "bool commit() override {\n";
				dump_commit_method(module);
				f << indent << "}\n";
				f << "\n";
				if (debug_info) {
					f << indent << "void debug_info(debug_items &items, std::string path = \"\") override {\n";
					dump_debug_info_method(module);
					f << indent << "}\n";
					f << "\n";
				}
				f << indent << "static std::unique_ptr<" << mangle(module);
				f << template_params(module, /*is_decl=*/false) << "> ";
				f << "create(std::string name, metadata_map parameters, metadata_map attributes);\n";
			dec_indent();
			f << indent << "}; // struct " << mangle(module) << "\n";
			f << "\n";
			if (blackbox_specializations.count(module)) {
				// If templated black boxes are used, the constructor of any module which includes the black box cell
				// (which calls the declared but not defined in the generated code `create` function) may only be used
				// if (a) the create function is defined in the same translation unit, or (b) the create function has
				// a forward-declared explicit specialization.
				//
				// Option (b) makes it possible to have the generated code and the black box implementation in different
				// translation units, which is convenient. Of course, its downside is that black boxes must predefine
				// a specialization for every combination of parameters the generated code may use; but since the main
				// purpose of templated black boxes is abstracting over datapath width, it is expected that there would
				// be very few such combinations anyway.
				for (auto specialization : blackbox_specializations[module]) {
					f << indent << "template<>\n";
					f << indent << "std::unique_ptr<" << mangle(module) << specialization << "> ";
					f << mangle(module) << specialization << "::";
					f << "create(std::string name, metadata_map parameters, metadata_map attributes);\n";
					f << "\n";
				}
			}
		} else {
			f << indent << "struct " << mangle(module) << " : public module {\n";
			inc_indent();
				for (auto wire : module->wires())
					dump_wire(wire, /*is_local=*/false);
				for (auto wire : module->wires())
					dump_debug_wire(wire, /*is_local=*/false);
				bool has_memories = false;
				for (auto memory : module->memories) {
					dump_memory(module, memory.second);
					has_memories = true;
				}
				if (has_memories)
					f << "\n";
				bool has_cells = false;
				for (auto cell : module->cells()) {
					if (is_internal_cell(cell->type))
						continue;
					dump_attrs(cell);
					RTLIL::Module *cell_module = module->design->module(cell->type);
					log_assert(cell_module != nullptr);
					if (cell_module->get_bool_attribute(ID(cxxrtl_blackbox))) {
						f << indent << "std::unique_ptr<" << mangle(cell_module) << template_args(cell) << "> ";
						f << mangle(cell) << " = " << mangle(cell_module) << template_args(cell);
						f << "::create(" << escape_cxx_string(get_hdl_name(cell)) << ", ";
						dump_metadata_map(cell->parameters);
						f << ", ";
						dump_metadata_map(cell->attributes);
						f << ");\n";
					} else {
						f << indent << mangle(cell_module) << " " << mangle(cell) << ";\n";
					}
					has_cells = true;
				}
				if (has_cells)
					f << "\n";
				f << indent << mangle(module) << "() {}\n";
				if (has_cells) {
					f << indent << mangle(module) << "(adopt, " << mangle(module) << " other) :\n";
					bool first = true;
					for (auto cell : module->cells()) {
						if (is_internal_cell(cell->type))
							continue;
						if (first) {
							first = false;
						} else {
							f << ",\n";
						}
						RTLIL::Module *cell_module = module->design->module(cell->type);
						if (cell_module->get_bool_attribute(ID(cxxrtl_blackbox))) {
							f << indent << "  " << mangle(cell) << "(std::move(other." << mangle(cell) << "))";
						} else {
							f << indent << "  " << mangle(cell) << "(adopt {}, std::move(other." << mangle(cell) << "))";
						}
					}
					f << " {\n";
					inc_indent();
						for (auto cell : module->cells()) {
							if (is_internal_cell(cell->type))
								continue;
							RTLIL::Module *cell_module = module->design->module(cell->type);
							if (cell_module->get_bool_attribute(ID(cxxrtl_blackbox)))
								f << indent << mangle(cell) << "->reset();\n";
						}
					dec_indent();
					f << indent << "}\n";
				} else {
					f << indent << mangle(module) << "(adopt, " << mangle(module) << " other) {}\n";
				}
				f << "\n";
				f << indent << "void reset() override {\n";
				inc_indent();
					f << indent << "*this = " << mangle(module) << "(adopt {}, std::move(*this));\n";
				dec_indent();
				f << indent << "}\n";
				f << "\n";
				f << indent << "bool eval() override;\n";
				f << indent << "bool commit() override;\n";
				if (debug_info) {
					if (debug_eval) {
						f << "\n";
						f << indent << "void debug_eval();\n";
						for (auto wire : module->wires())
							if (debug_wire_types[wire].is_outline()) {
								f << indent << "debug_outline debug_eval_outline { std::bind(&"
								            << mangle(module) << "::debug_eval, this) };\n";
								break;
							}
					}
					f << "\n";
					f << indent << "void debug_info(debug_items &items, std::string path = \"\") override;\n";
				}
			dec_indent();
			f << indent << "}; // struct " << mangle(module) << "\n";
			f << "\n";
		}
	}

	void dump_module_impl(RTLIL::Module *module)
	{
		if (module->get_bool_attribute(ID(cxxrtl_blackbox)))
			return;
		f << indent << "bool " << mangle(module) << "::eval() {\n";
		dump_eval_method(module);
		f << indent << "}\n";
		f << "\n";
		f << indent << "bool " << mangle(module) << "::commit() {\n";
		dump_commit_method(module);
		f << indent << "}\n";
		f << "\n";
		if (debug_info) {
			if (debug_eval) {
				f << indent << "void " << mangle(module) << "::debug_eval() {\n";
				dump_debug_eval_method(module);
				f << indent << "}\n";
				f << "\n";
			}
			f << indent << "CXXRTL_EXTREMELY_COLD\n";
			f << indent << "void " << mangle(module) << "::debug_info(debug_items &items, std::string path) {\n";
			dump_debug_info_method(module);
			f << indent << "}\n";
			f << "\n";
		}
	}

	void dump_design(RTLIL::Design *design)
	{
		RTLIL::Module *top_module = nullptr;
		std::vector<RTLIL::Module*> modules;
		TopoSort<RTLIL::Module*> topo_design;
		for (auto module : design->modules()) {
			if (!design->selected_module(module))
				continue;
			if (module->get_bool_attribute(ID(cxxrtl_blackbox)))
				modules.push_back(module); // cxxrtl blackboxes first
			if (module->get_blackbox_attribute() || module->get_bool_attribute(ID(cxxrtl_blackbox)))
				continue;
			if (module->get_bool_attribute(ID::top))
				top_module = module;

			topo_design.node(module);
			for (auto cell : module->cells()) {
				if (is_internal_cell(cell->type) || is_cxxrtl_blackbox_cell(cell))
					continue;
				RTLIL::Module *cell_module = design->module(cell->type);
				log_assert(cell_module != nullptr);
				topo_design.edge(cell_module, module);
			}
		}
		bool no_loops = topo_design.sort();
		log_assert(no_loops);
		modules.insert(modules.end(), topo_design.sorted.begin(), topo_design.sorted.end());

		if (split_intf) {
			// The only thing more depraved than include guards, is mangling filenames to turn them into include guards.
			std::string include_guard = design_ns + "_header";
			std::transform(include_guard.begin(), include_guard.end(), include_guard.begin(), ::toupper);

			f << "#ifndef " << include_guard << "\n";
			f << "#define " << include_guard << "\n";
			f << "\n";
			if (top_module != nullptr && debug_info) {
				f << "#include <backends/cxxrtl/cxxrtl_capi.h>\n";
				f << "\n";
				f << "#ifdef __cplusplus\n";
				f << "extern \"C\" {\n";
				f << "#endif\n";
				f << "\n";
				f << "cxxrtl_toplevel " << design_ns << "_create();\n";
				f << "\n";
				f << "#ifdef __cplusplus\n";
				f << "}\n";
				f << "#endif\n";
				f << "\n";
			} else {
				f << "// The CXXRTL C API is not available because the design is built without debug information.\n";
				f << "\n";
			}
			f << "#ifdef __cplusplus\n";
			f << "\n";
			f << "#include <backends/cxxrtl/cxxrtl.h>\n";
			f << "\n";
			f << "using namespace cxxrtl;\n";
			f << "\n";
			f << "namespace " << design_ns << " {\n";
			f << "\n";
			for (auto module : modules)
				dump_module_intf(module);
			f << "} // namespace " << design_ns << "\n";
			f << "\n";
			f << "#endif // __cplusplus\n";
			f << "\n";
			f << "#endif\n";
			*intf_f << f.str(); f.str("");
		}

		if (split_intf)
			f << "#include \"" << intf_filename << "\"\n";
		else
			f << "#include <backends/cxxrtl/cxxrtl.h>\n";
		f << "\n";
		f << "#if defined(CXXRTL_INCLUDE_CAPI_IMPL) || \\\n";
		f << "    defined(CXXRTL_INCLUDE_VCD_CAPI_IMPL)\n";
		f << "#include <backends/cxxrtl/cxxrtl_capi.cc>\n";
		f << "#endif\n";
		f << "\n";
		f << "#if defined(CXXRTL_INCLUDE_VCD_CAPI_IMPL)\n";
		f << "#include <backends/cxxrtl/cxxrtl_vcd_capi.cc>\n";
		f << "#endif\n";
		f << "\n";
		f << "using namespace cxxrtl_yosys;\n";
		f << "\n";
		f << "namespace " << design_ns << " {\n";
		f << "\n";
		for (auto module : modules) {
			if (!split_intf)
				dump_module_intf(module);
			dump_module_impl(module);
		}
		f << "} // namespace " << design_ns << "\n";
		f << "\n";
		if (top_module != nullptr && debug_info) {
			f << "extern \"C\"\n";
			f << "cxxrtl_toplevel " << design_ns << "_create() {\n";
			inc_indent();
				std::string top_type = design_ns + "::" + mangle(top_module);
				f << indent << "return new _cxxrtl_toplevel { ";
				f << "std::unique_ptr<" << top_type << ">(new " + top_type + ")";
				f << " };\n";
			dec_indent();
			f << "}\n";
		}

		*impl_f << f.str(); f.str("");
	}

	// Edge-type sync rules require us to emit edge detectors, which require coordination between
	// eval and commit phases. To do this we need to collect them upfront.
	//
	// Note that the simulator commit phase operates at wire granularity but edge-type sync rules
	// operate at wire bit granularity; it is possible to have code similar to:
	//     wire [3:0] clocks;
	//     always @(posedge clocks[0]) ...
	// To handle this we track edge sensitivity both for wires and wire bits.
	void register_edge_signal(SigMap &sigmap, RTLIL::SigSpec signal, RTLIL::SyncType type)
	{
		signal = sigmap(signal);
		if (signal.is_fully_const())
			return; // a clock, or more commonly a reset, can be tied to a constant driver
		log_assert(is_valid_clock(signal));
		log_assert(type == RTLIL::STp || type == RTLIL::STn || type == RTLIL::STe);

		RTLIL::SigBit sigbit = signal[0];
		if (!edge_types.count(sigbit))
			edge_types[sigbit] = type;
		else if (edge_types[sigbit] != type)
			edge_types[sigbit] = RTLIL::STe;
		// Cannot use as_wire because signal might not be a full wire, instead extract the wire from the sigbit
		edge_wires.insert(sigbit.wire);
	}

	void analyze_design(RTLIL::Design *design)
	{
		bool has_feedback_arcs = false;
		bool has_buffered_comb_wires = false;

		for (auto module : design->modules()) {
			if (!design->selected_module(module))
				continue;

			SigMap &sigmap = sigmaps[module];
			sigmap.set(module);

			if (module->get_bool_attribute(ID(cxxrtl_blackbox))) {
				for (auto port : module->ports) {
					RTLIL::Wire *wire = module->wire(port);
					if (wire->port_input && !wire->port_output) {
						wire_types[wire] = debug_wire_types[wire] = {WireType::MEMBER};
					} else if (wire->port_input || wire->port_output) {
						wire_types[wire] = debug_wire_types[wire] = {WireType::BUFFERED};
					}
					if (wire->has_attribute(ID(cxxrtl_edge))) {
						RTLIL::Const edge_attr = wire->attributes[ID(cxxrtl_edge)];
						if (!(edge_attr.flags & RTLIL::CONST_FLAG_STRING) || (int)edge_attr.decode_string().size() != GetSize(wire))
							log_cmd_error("Attribute `cxxrtl_edge' of port `%s.%s' is not a string with one character per bit.\n",
							              log_id(module), log_signal(wire));

						std::string edges = wire->get_string_attribute(ID(cxxrtl_edge));
						for (int i = 0; i < GetSize(wire); i++) {
							RTLIL::SigSpec wire_sig = wire;
							switch (edges[i]) {
								case '-': break;
								case 'p': register_edge_signal(sigmap, wire_sig[i], RTLIL::STp); break;
								case 'n': register_edge_signal(sigmap, wire_sig[i], RTLIL::STn); break;
								case 'a': register_edge_signal(sigmap, wire_sig[i], RTLIL::STe); break;
								default:
									log_cmd_error("Attribute `cxxrtl_edge' of port `%s.%s' contains specifiers "
									              "other than '-', 'p', 'n', or 'a'.\n",
										log_id(module), log_signal(wire));
							}
						}
					}
				}

				// Black boxes converge by default, since their implementations are quite unlikely to require
				// internal propagation of comb signals.
				eval_converges[module] = true;
				continue;
			}

			// Construct a flow graph where each node is a basic computational operation generally corresponding
			// to a fragment of the RTLIL netlist.
			FlowGraph flow;

			for (auto conn : module->connections())
				flow.add_node(conn);

			dict<const RTLIL::Cell*, FlowGraph::Node*> memrw_cell_nodes;
			dict<std::pair<RTLIL::SigBit, const RTLIL::Memory*>,
			     pool<const RTLIL::Cell*>> memwr_per_domain;
			for (auto cell : module->cells()) {
				if (!cell->known())
					log_cmd_error("Unknown cell `%s'.\n", log_id(cell->type));

				RTLIL::Module *cell_module = design->module(cell->type);
				if (cell_module &&
				    cell_module->get_blackbox_attribute() &&
				    !cell_module->get_bool_attribute(ID(cxxrtl_blackbox)))
					log_cmd_error("External blackbox cell `%s' is not marked as a CXXRTL blackbox.\n", log_id(cell->type));

				if (cell_module &&
				    cell_module->get_bool_attribute(ID(cxxrtl_blackbox)) &&
				    cell_module->get_bool_attribute(ID(cxxrtl_template)))
					blackbox_specializations[cell_module].insert(template_args(cell));

				FlowGraph::Node *node = flow.add_node(cell);

				// Various DFF cells are treated like posedge/negedge processes, see above for details.
				if (cell->type.in(ID($dff), ID($dffe), ID($adff), ID($adffe), ID($dffsr), ID($dffsre), ID($sdff), ID($sdffe), ID($sdffce))) {
					if (is_valid_clock(cell->getPort(ID::CLK)))
						register_edge_signal(sigmap, cell->getPort(ID::CLK),
							cell->parameters[ID::CLK_POLARITY].as_bool() ? RTLIL::STp : RTLIL::STn);
				}
				// Similar for memory port cells.
				if (cell->type.in(ID($memrd), ID($memwr))) {
					if (cell->getParam(ID::CLK_ENABLE).as_bool()) {
						if (is_valid_clock(cell->getPort(ID::CLK)))
							register_edge_signal(sigmap, cell->getPort(ID::CLK),
								cell->parameters[ID::CLK_POLARITY].as_bool() ? RTLIL::STp : RTLIL::STn);
					}
					memrw_cell_nodes[cell] = node;
				}
				// Optimize access to read-only memories.
				if (cell->type == ID($memwr))
					writable_memories.insert(module->memories[cell->getParam(ID::MEMID).decode_string()]);
				// Collect groups of memory write ports in the same domain.
				if (cell->type == ID($memwr) && cell->getParam(ID::CLK_ENABLE).as_bool() && is_valid_clock(cell->getPort(ID::CLK))) {
					RTLIL::SigBit clk_bit = sigmap(cell->getPort(ID::CLK))[0];
					const RTLIL::Memory *memory = module->memories[cell->getParam(ID::MEMID).decode_string()];
					memwr_per_domain[{clk_bit, memory}].insert(cell);
				}
				// Handling of packed memories is delegated to the `memory_unpack` pass, so we can rely on the presence
				// of RTLIL memory objects and $memrd/$memwr/$meminit cells.
				if (cell->type.in(ID($mem)))
					log_assert(false);
			}
			for (auto cell : module->cells()) {
				// Collect groups of memory write ports read by every transparent read port.
				if (cell->type == ID($memrd) && cell->getParam(ID::CLK_ENABLE).as_bool() && is_valid_clock(cell->getPort(ID::CLK)) &&
				    cell->getParam(ID::TRANSPARENT).as_bool()) {
					RTLIL::SigBit clk_bit = sigmap(cell->getPort(ID::CLK))[0];
					const RTLIL::Memory *memory = module->memories[cell->getParam(ID::MEMID).decode_string()];
					for (auto memwr_cell : memwr_per_domain[{clk_bit, memory}]) {
						transparent_for[cell].insert(memwr_cell);
						// Our implementation of transparent $memrd cells reads \EN, \ADDR and \DATA from every $memwr cell
						// in the same domain, which isn't directly visible in the netlist. Add these uses explicitly.
						flow.add_uses(memrw_cell_nodes[cell], memwr_cell->getPort(ID::EN));
						flow.add_uses(memrw_cell_nodes[cell], memwr_cell->getPort(ID::ADDR));
						flow.add_uses(memrw_cell_nodes[cell], memwr_cell->getPort(ID::DATA));
					}
				}
			}

			for (auto proc : module->processes) {
				flow.add_node(proc.second);

				for (auto sync : proc.second->syncs)
					switch (sync->type) {
						// Edge-type sync rules require pre-registration.
						case RTLIL::STp:
						case RTLIL::STn:
						case RTLIL::STe:
							register_edge_signal(sigmap, sync->signal, sync->type);
							break;

						// Level-type sync rules require no special handling.
						case RTLIL::ST0:
						case RTLIL::ST1:
						case RTLIL::STa:
							break;

						case RTLIL::STg:
							log_cmd_error("Global clock is not supported.\n");

						// Handling of init-type sync rules is delegated to the `proc_init` pass, so we can use the wire
						// attribute regardless of input.
						case RTLIL::STi:
							log_assert(false);
					}
			}

			// Construct a linear order of the flow graph that minimizes the amount of feedback arcs. A flow graph
			// without feedback arcs can generally be evaluated in a single pass, i.e. it always requires only
			// a single delta cycle.
			Scheduler<FlowGraph::Node> scheduler;
			dict<FlowGraph::Node*, Scheduler<FlowGraph::Node>::Vertex*, hash_ptr_ops> node_vertex_map;
			for (auto node : flow.nodes)
				node_vertex_map[node] = scheduler.add(node);
			for (auto node_comb_def : flow.node_comb_defs) {
				auto vertex = node_vertex_map[node_comb_def.first];
				for (auto wire : node_comb_def.second)
					for (auto succ_node : flow.wire_uses[wire]) {
						auto succ_vertex = node_vertex_map[succ_node];
						vertex->succs.insert(succ_vertex);
						succ_vertex->preds.insert(vertex);
					}
			}

			// Find out whether the order includes any feedback arcs.
			std::vector<FlowGraph::Node*> node_order;
			pool<FlowGraph::Node*, hash_ptr_ops> evaluated_nodes;
			pool<const RTLIL::Wire*> feedback_wires;
			for (auto vertex : scheduler.schedule()) {
				auto node = vertex->data;
				node_order.push_back(node);
				// Any wire that is an output of node vo and input of node vi where vo is scheduled later than vi
				// is a feedback wire. Feedback wires indicate apparent logic loops in the design, which may be
				// caused by a true logic loop, but usually are a benign result of dependency tracking that works
				// on wire, not bit, level. Nevertheless, feedback wires cannot be unbuffered.
				evaluated_nodes.insert(node);
				for (auto wire : flow.node_comb_defs[node])
					for (auto succ_node : flow.wire_uses[wire])
						if (evaluated_nodes[succ_node])
							feedback_wires.insert(wire);
			}
			if (!feedback_wires.empty()) {
				has_feedback_arcs = true;
				log("Module `%s' contains feedback arcs through wires:\n", log_id(module));
				for (auto wire : feedback_wires)
					log("  %s\n", log_id(wire));
			}

			// Conservatively assign wire types. Assignment of types BUFFERED and MEMBER is final, but assignment
			// of type LOCAL may be further refined to UNUSED or INLINE.
			for (auto wire : module->wires()) {
				auto &wire_type = wire_types[wire];
				wire_type = {WireType::BUFFERED};

				if (feedback_wires[wire]) continue;
				if (wire->port_output && !module->get_bool_attribute(ID::top)) continue;
				if (!wire->name.isPublic() && !unbuffer_internal) continue;
				if (wire->name.isPublic() && !unbuffer_public) continue;
				if (flow.wire_sync_defs.count(wire) > 0) continue;
				wire_type = {WireType::MEMBER};

				if (edge_wires[wire]) continue;
				if (wire->get_bool_attribute(ID::keep)) continue;
				if (wire->port_input || wire->port_output) continue;
				if (!wire->name.isPublic() && !localize_internal) continue;
				if (wire->name.isPublic() && !localize_public) continue;
				wire_type = {WireType::LOCAL};
			}

			// Discover nodes reachable from primary outputs (i.e. members) and collect reachable wire users.
			pool<FlowGraph::Node*, hash_ptr_ops> worklist;
			for (auto node : flow.nodes) {
				if (node->type == FlowGraph::Node::Type::CELL_EVAL && is_effectful_cell(node->cell->type))
					worklist.insert(node); // node has effects
				else if (flow.node_sync_defs.count(node))
					worklist.insert(node); // node is a flip-flop
				else if (flow.node_comb_defs.count(node)) {
					for (auto wire : flow.node_comb_defs[node])
						if (wire_types[wire].is_member())
							worklist.insert(node); // node drives public wires
				}
			}
			dict<const RTLIL::Wire*, pool<FlowGraph::Node*, hash_ptr_ops>> live_wires;
			pool<FlowGraph::Node*, hash_ptr_ops> live_nodes;
			while (!worklist.empty()) {
				auto node = worklist.pop();
				live_nodes.insert(node);
				for (auto wire : flow.node_uses[node]) {
					live_wires[wire].insert(node);
					for (auto pred_node : flow.wire_comb_defs[wire])
						if (!live_nodes[pred_node])
							worklist.insert(pred_node);
				}
			}

			// Refine wire types taking into account the amount of uses from reachable nodes only.
			for (auto wire : module->wires()) {
				auto &wire_type = wire_types[wire];
				if (!wire_type.is_local()) continue;
				if (!wire->name.isPublic() && !inline_internal) continue;
				if (wire->name.isPublic() && !inline_public) continue;

				if (live_wires[wire].empty()) {
					wire_type = {WireType::UNUSED}; // wire never used
				} else if (flow.is_inlinable(wire, live_wires[wire])) {
					if (flow.wire_comb_defs[wire].size() > 1)
						log_cmd_error("Wire %s.%s has multiple drivers!\n", log_id(module), log_id(wire));
					log_assert(flow.wire_comb_defs[wire].size() == 1);
					FlowGraph::Node *node = *flow.wire_comb_defs[wire].begin();
					switch (node->type) {
						case FlowGraph::Node::Type::CELL_EVAL:
							if (!is_inlinable_cell(node->cell->type)) continue;
							wire_type = {WireType::INLINE, node->cell}; // wire replaced with cell
							break;
						case FlowGraph::Node::Type::CONNECT:
							wire_type = {WireType::INLINE, node->connect.second}; // wire replaced with sig
							break;
						default: continue;
					}
					live_nodes.erase(node);
				}
			}

			// Emit reachable nodes in eval().
			for (auto node : node_order)
				if (live_nodes[node])
					schedule[module].push_back(*node);

			// For maximum performance, the state of the simulation (which is the same as the set of its double buffered
			// wires, since using a singly buffered wire for any kind of state introduces a race condition) should contain
			// no wires attached to combinatorial outputs. Feedback wires, by definition, make that impossible. However,
			// it is possible that a design with no feedback arcs would end up with doubly buffered wires in such cases
			// as a wire with multiple drivers where one of them is combinatorial and the other is synchronous. Such designs
			// also require more than one delta cycle to converge.
			pool<const RTLIL::Wire*> buffered_comb_wires;
			for (auto wire : module->wires())
				if (wire_types[wire].is_buffered() && !feedback_wires[wire] && flow.wire_comb_defs[wire].size() > 0)
					buffered_comb_wires.insert(wire);
			if (!buffered_comb_wires.empty()) {
				has_buffered_comb_wires = true;
				log("Module `%s' contains buffered combinatorial wires:\n", log_id(module));
				for (auto wire : buffered_comb_wires)
					log("  %s\n", log_id(wire));
			}

			// Record whether eval() requires only one delta cycle in this module.
			eval_converges[module] = feedback_wires.empty() && buffered_comb_wires.empty();

			if (debug_info) {
				// Annotate wire bits with the type of their driver; this is exposed in the debug metadata.
				for (auto item : flow.bit_has_state)
					bit_has_state.insert(item);

				// Assign debug information wire types to public wires according to the chosen debug level.
				// Unlike with optimized wire types, all assignments here are final.
				for (auto wire : module->wires()) {
					const auto &wire_type = wire_types[wire];
					auto &debug_wire_type = debug_wire_types[wire];
					if (wire_type.type == WireType::UNUSED) continue;
					if (!wire->name.isPublic()) continue;

					if (!debug_info) continue;
					if (wire->port_input || wire_type.is_buffered())
						debug_wire_type = wire_type; // wire contains state

					if (!debug_member) continue;
					if (wire_type.is_member())
						debug_wire_type = wire_type; // wire is a member

					if (!debug_alias) continue;
					const RTLIL::Wire *it = wire;
					while (flow.is_inlinable(it)) {
						log_assert(flow.wire_comb_defs[it].size() == 1);
						FlowGraph::Node *node = *flow.wire_comb_defs[it].begin();
						if (node->type != FlowGraph::Node::Type::CONNECT) break; // not an alias
						RTLIL::SigSpec rhs = node->connect.second;
						if (rhs.is_fully_const()) {
						  debug_wire_type = {WireType::CONST, rhs}; // wire replaced with const
						} else if (rhs.is_wire()) {
							if (wire_types[rhs.as_wire()].is_member())
								debug_wire_type = {WireType::ALIAS, rhs}; // wire replaced with wire
							else if (debug_eval && rhs.as_wire()->name.isPublic())
								debug_wire_type = {WireType::ALIAS, rhs}; // wire replaced with outline
							it = rhs.as_wire(); // and keep looking
							continue;
						}
						break;
					}

					if (!debug_eval) continue;
					if (!debug_wire_type.is_exact() && !wire_type.is_member())
						debug_wire_type = {WireType::OUTLINE}; // wire is local or inlined
				}

				// Discover nodes reachable from primary outputs (i.e. outlines) up until primary inputs (i.e. members)
				// and collect reachable wire users.
				pool<FlowGraph::Node*, hash_ptr_ops> worklist;
				for (auto node : flow.nodes) {
					if (flow.node_comb_defs.count(node))
						for (auto wire : flow.node_comb_defs[node])
							if (debug_wire_types[wire].is_outline())
								worklist.insert(node); // node drives outline
				}
				dict<const RTLIL::Wire*, pool<FlowGraph::Node*, hash_ptr_ops>> debug_live_wires;
				pool<FlowGraph::Node*, hash_ptr_ops> debug_live_nodes;
				while (!worklist.empty()) {
					auto node = worklist.pop();
					debug_live_nodes.insert(node);
					for (auto wire : flow.node_uses[node]) {
						if (debug_wire_types[wire].is_member())
							continue; // node uses member
						if (debug_wire_types[wire].is_exact())
							continue; // node uses alias or const
						debug_live_wires[wire].insert(node);
						for (auto pred_node : flow.wire_comb_defs[wire])
							if (!debug_live_nodes[pred_node])
								worklist.insert(pred_node);
					}
				}

				// Assign debug information wire types to internal wires used by reachable nodes. This is similar
				// to refining optimized wire types with the exception that the assignments here are first and final.
				for (auto wire : module->wires()) {
					const auto &wire_type = wire_types[wire];
					auto &debug_wire_type = debug_wire_types[wire];
					if (wire->name.isPublic()) continue;

					if (live_wires[wire].empty() || debug_live_wires[wire].empty()) {
						continue; // wire never used
					} else if (flow.is_inlinable(wire, debug_live_wires[wire])) {
						log_assert(flow.wire_comb_defs[wire].size() == 1);
						FlowGraph::Node *node = *flow.wire_comb_defs[wire].begin();
						switch (node->type) {
							case FlowGraph::Node::Type::CELL_EVAL:
								if (!is_inlinable_cell(node->cell->type)) continue;
								debug_wire_type = {WireType::INLINE, node->cell}; // wire replaced with cell
								break;
							case FlowGraph::Node::Type::CONNECT:
							  debug_wire_type = {WireType::INLINE, node->connect.second}; // wire replaced with sig
								break;
							default: continue;
						}
						debug_live_nodes.erase(node);
					} else if (wire_type.is_local()) {
						debug_wire_type = {WireType::LOCAL}; // wire not inlinable
					} else {
						log_assert(wire_type.is_member());
						debug_wire_type = wire_type; // wire is a member
					}
				}

				// Emit reachable nodes in debug_eval().
				for (auto node : node_order)
					if (debug_live_nodes[node])
						debug_schedule[module].push_back(*node);
			}

			auto show_wire_type = [&](const RTLIL::Wire* wire, const WireType &wire_type) {
				const char *type_str;
				switch (wire_type.type) {
					case WireType::UNUSED:   type_str = "UNUSED";   break;
					case WireType::BUFFERED: type_str = "BUFFERED"; break;
					case WireType::MEMBER:   type_str = "MEMBER";   break;
					case WireType::OUTLINE:  type_str = "OUTLINE";  break;
					case WireType::LOCAL:    type_str = "LOCAL";    break;
					case WireType::INLINE:   type_str = "INLINE";   break;
					case WireType::ALIAS:    type_str = "ALIAS";    break;
					case WireType::CONST:    type_str = "CONST";    break;
					default:                 type_str = "(invalid)";
				}
				if (wire_type.sig_subst.empty())
					log_debug("  %s: %s\n", log_signal((RTLIL::Wire*)wire), type_str);
				else
					log_debug("  %s: %s = %s\n", log_signal((RTLIL::Wire*)wire), type_str, log_signal(wire_type.sig_subst));
			};
			if (print_wire_types && !wire_types.empty()) {
				log_debug("Wire types:\n");
				for (auto wire_type : wire_types)
					show_wire_type(wire_type.first, wire_type.second);
			}
			if (print_debug_wire_types && !debug_wire_types.empty()) {
				log_debug("Debug wire types:\n");
				for (auto debug_wire_type : debug_wire_types)
					show_wire_type(debug_wire_type.first, debug_wire_type.second);
			}
		}
		if (has_feedback_arcs || has_buffered_comb_wires) {
			// Although both non-feedback buffered combinatorial wires and apparent feedback wires may be eliminated
			// by optimizing the design, if after `proc; flatten` there are any feedback wires remaining, it is very
			// likely that these feedback wires are indicative of a true logic loop, so they get emphasized in the message.
			const char *why_pessimistic = nullptr;
			if (has_feedback_arcs)
				why_pessimistic = "feedback wires";
			else if (has_buffered_comb_wires)
				why_pessimistic = "buffered combinatorial wires";
			log_warning("Design contains %s, which require delta cycles during evaluation.\n", why_pessimistic);
			if (!run_flatten)
				log("Flattening may eliminate %s from the design.\n", why_pessimistic);
			if (!run_proc)
				log("Converting processes to netlists may eliminate %s from the design.\n", why_pessimistic);
		}
	}

	void check_design(RTLIL::Design *design, bool &has_top, bool &has_sync_init, bool &has_packed_mem)
	{
		has_sync_init = has_packed_mem = has_top = false;

		for (auto module : design->modules()) {
			if (module->get_blackbox_attribute() && !module->has_attribute(ID(cxxrtl_blackbox)))
				continue;

			if (!design->selected_whole_module(module))
				if (design->selected_module(module))
					log_cmd_error("Can't handle partially selected module `%s'!\n", id2cstr(module->name));
			if (!design->selected_module(module))
				continue;

			if (module->get_bool_attribute(ID::top))
				has_top = true;

			for (auto proc : module->processes)
				for (auto sync : proc.second->syncs)
					if (sync->type == RTLIL::STi)
						has_sync_init = true;

			// The Mem constructor also checks for well-formedness of $meminit cells, if any.
			for (auto &mem : Mem::get_all_memories(module))
				if (mem.packed)
					has_packed_mem = true;
		}
	}

	void prepare_design(RTLIL::Design *design)
	{
		bool did_anything = false;
		bool has_top, has_sync_init, has_packed_mem;
		log_push();
		check_design(design, has_top, has_sync_init, has_packed_mem);
		if (run_hierarchy && !has_top) {
			Pass::call(design, "hierarchy -auto-top");
			did_anything = true;
		}
		if (run_flatten) {
			Pass::call(design, "flatten");
			did_anything = true;
		}
		if (run_proc) {
			Pass::call(design, "proc");
			did_anything = true;
		} else if (has_sync_init) {
			// We're only interested in proc_init, but it depends on proc_prune and proc_clean, so call those
			// in case they weren't already. (This allows `yosys foo.v -o foo.cc` to work.)
			Pass::call(design, "proc_prune");
			Pass::call(design, "proc_clean");
			Pass::call(design, "proc_init");
			did_anything = true;
		}
		if (has_packed_mem) {
			Pass::call(design, "memory_unpack");
			did_anything = true;
		}
		// Recheck the design if it was modified.
		if (did_anything)
			check_design(design, has_top, has_sync_init, has_packed_mem);
		log_assert(!has_sync_init && !has_packed_mem);
		log_pop();
		if (did_anything)
			log_spacer();
		analyze_design(design);
	}
};

struct CxxrtlBackend : public Backend {
	static const int DEFAULT_OPT_LEVEL = 6;
	static const int DEFAULT_DEBUG_LEVEL = 4;

	CxxrtlBackend() : Backend("cxxrtl", "convert design to C++ RTL simulation") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    write_cxxrtl [options] [filename]\n");
		log("\n");
		log("Write C++ code that simulates the design. The generated code requires a driver\n");
		log("that instantiates the design, toggles its clock, and interacts with its ports.\n");
		log("\n");
		log("The following driver may be used as an example for a design with a single clock\n");
		log("driving rising edge triggered flip-flops:\n");
		log("\n");
		log("    #include \"top.cc\"\n");
		log("\n");
		log("    int main() {\n");
		log("      cxxrtl_design::p_top top;\n");
		log("      top.step();\n");
		log("      while (1) {\n");
		log("        /* user logic */\n");
		log("        top.p_clk.set(false);\n");
		log("        top.step();\n");
		log("        top.p_clk.set(true);\n");
		log("        top.step();\n");
		log("      }\n");
		log("    }\n");
		log("\n");
		log("Note that CXXRTL simulations, just like the hardware they are simulating, are\n");
		log("subject to race conditions. If, in the example above, the user logic would run\n");
		log("simultaneously with the rising edge of the clock, the design would malfunction.\n");
		log("\n");
		log("This backend supports replacing parts of the design with black boxes implemented\n");
		log("in C++. If a module marked as a CXXRTL black box, its implementation is ignored,\n");
		log("and the generated code consists only of an interface and a factory function.\n");
		log("The driver must implement the factory function that creates an implementation of\n");
		log("the black box, taking into account the parameters it is instantiated with.\n");
		log("\n");
		log("For example, the following Verilog code defines a CXXRTL black box interface for\n");
		log("a synchronous debug sink:\n");
		log("\n");
		log("    (* cxxrtl_blackbox *)\n");
		log("    module debug(...);\n");
		log("      (* cxxrtl_edge = \"p\" *) input clk;\n");
		log("      input en;\n");
		log("      input [7:0] i_data;\n");
		log("      (* cxxrtl_sync *) output [7:0] o_data;\n");
		log("    endmodule\n");
		log("\n");
		log("For this HDL interface, this backend will generate the following C++ interface:\n");
		log("\n");
		log("    struct bb_p_debug : public module {\n");
		log("      value<1> p_clk;\n");
		log("      bool posedge_p_clk() const { /* ... */ }\n");
		log("      value<1> p_en;\n");
		log("      value<8> p_i_data;\n");
		log("      wire<8> p_o_data;\n");
		log("\n");
		log("      bool eval() override;\n");
		log("      bool commit() override;\n");
		log("\n");
		log("      static std::unique_ptr<bb_p_debug>\n");
		log("      create(std::string name, metadata_map parameters, metadata_map attributes);\n");
		log("    };\n");
		log("\n");
		log("The `create' function must be implemented by the driver. For example, it could\n");
		log("always provide an implementation logging the values to standard error stream:\n");
		log("\n");
		log("    namespace cxxrtl_design {\n");
		log("\n");
		log("    struct stderr_debug : public bb_p_debug {\n");
		log("      bool eval() override {\n");
		log("        if (posedge_p_clk() && p_en)\n");
		log("          fprintf(stderr, \"debug: %%02x\\n\", p_i_data.data[0]);\n");
		log("        p_o_data.next = p_i_data;\n");
		log("        return bb_p_debug::eval();\n");
		log("      }\n");
		log("    };\n");
		log("\n");
		log("    std::unique_ptr<bb_p_debug>\n");
		log("    bb_p_debug::create(std::string name, cxxrtl::metadata_map parameters,\n");
		log("                       cxxrtl::metadata_map attributes) {\n");
		log("      return std::make_unique<stderr_debug>();\n");
		log("    }\n");
		log("\n");
		log("    }\n");
		log("\n");
		log("For complex applications of black boxes, it is possible to parameterize their\n");
		log("port widths. For example, the following Verilog code defines a CXXRTL black box\n");
		log("interface for a configurable width debug sink:\n");
		log("\n");
		log("    (* cxxrtl_blackbox, cxxrtl_template = \"WIDTH\" *)\n");
		log("    module debug(...);\n");
		log("      parameter WIDTH = 8;\n");
		log("      (* cxxrtl_edge = \"p\" *) input clk;\n");
		log("      input en;\n");
		log("      (* cxxrtl_width = \"WIDTH\" *) input [WIDTH - 1:0] i_data;\n");
		log("      (* cxxrtl_width = \"WIDTH\" *) output [WIDTH - 1:0] o_data;\n");
		log("    endmodule\n");
		log("\n");
		log("For this parametric HDL interface, this backend will generate the following C++\n");
		log("interface (only the differences are shown):\n");
		log("\n");
		log("    template<size_t WIDTH>\n");
		log("    struct bb_p_debug : public module {\n");
		log("      // ...\n");
		log("      value<WIDTH> p_i_data;\n");
		log("      wire<WIDTH> p_o_data;\n");
		log("      // ...\n");
		log("      static std::unique_ptr<bb_p_debug<WIDTH>>\n");
		log("      create(std::string name, metadata_map parameters, metadata_map attributes);\n");
		log("    };\n");
		log("\n");
		log("The `create' function must be implemented by the driver, specialized for every\n");
		log("possible combination of template parameters. (Specialization is necessary to\n");
		log("enable separate compilation of generated code and black box implementations.)\n");
		log("\n");
		log("    template<size_t SIZE>\n");
		log("    struct stderr_debug : public bb_p_debug<SIZE> {\n");
		log("      // ...\n");
		log("    };\n");
		log("\n");
		log("    template<>\n");
		log("    std::unique_ptr<bb_p_debug<8>>\n");
		log("    bb_p_debug<8>::create(std::string name, cxxrtl::metadata_map parameters,\n");
		log("                          cxxrtl::metadata_map attributes) {\n");
		log("      return std::make_unique<stderr_debug<8>>();\n");
		log("    }\n");
		log("\n");
		log("The following attributes are recognized by this backend:\n");
		log("\n");
		log("    cxxrtl_blackbox\n");
		log("        only valid on modules. if specified, the module contents are ignored,\n");
		log("        and the generated code includes only the module interface and a factory\n");
		log("        function, which will be called to instantiate the module.\n");
		log("\n");
		log("    cxxrtl_edge\n");
		log("        only valid on inputs of black boxes. must be one of \"p\", \"n\", \"a\".\n");
		log("        if specified on signal `clk`, the generated code includes edge detectors\n");
		log("        `posedge_p_clk()` (if \"p\"), `negedge_p_clk()` (if \"n\"), or both (if\n");
		log("        \"a\"), simplifying implementation of clocked black boxes.\n");
		log("\n");
		log("    cxxrtl_template\n");
		log("        only valid on black boxes. must contain a space separated sequence of\n");
		log("        identifiers that have a corresponding black box parameters. for each\n");
		log("        of them, the generated code includes a `size_t` template parameter.\n");
		log("\n");
		log("    cxxrtl_width\n");
		log("        only valid on ports of black boxes. must be a constant expression, which\n");
		log("        is directly inserted into generated code.\n");
		log("\n");
		log("    cxxrtl_comb, cxxrtl_sync\n");
		log("        only valid on outputs of black boxes. if specified, indicates that every\n");
		log("        bit of the output port is driven, correspondingly, by combinatorial or\n");
		log("        synchronous logic. this knowledge is used for scheduling optimizations.\n");
		log("        if neither is specified, the output will be pessimistically treated as\n");
		log("        driven by both combinatorial and synchronous logic.\n");
		log("\n");
		log("The following options are supported by this backend:\n");
		log("\n");
		log("    -print-wire-types, -print-debug-wire-types\n");
		log("        enable additional debug logging, for pass developers.\n");
		log("\n");
		log("    -header\n");
		log("        generate separate interface (.h) and implementation (.cc) files.\n");
		log("        if specified, the backend must be called with a filename, and filename\n");
		log("        of the interface is derived from filename of the implementation.\n");
		log("        otherwise, interface and implementation are generated together.\n");
		log("\n");
		log("    -namespace <ns-name>\n");
		log("        place the generated code into namespace <ns-name>. if not specified,\n");
		log("        \"cxxrtl_design\" is used.\n");
		log("\n");
		log("    -nohierarchy\n");
		log("        use design hierarchy as-is. in most designs, a top module should be\n");
		log("        present as it is exposed through the C API and has unbuffered outputs\n");
		log("        for improved performance; it will be determined automatically if absent.\n");
		log("\n");
		log("    -noflatten\n");
		log("        don't flatten the design. fully flattened designs can evaluate within\n");
		log("        one delta cycle if they have no combinatorial feedback.\n");
		log("        note that the debug interface and waveform dumps use full hierarchical\n");
		log("        names for all wires even in flattened designs.\n");
		log("\n");
		log("    -noproc\n");
		log("        don't convert processes to netlists. in most designs, converting\n");
		log("        processes significantly improves evaluation performance at the cost of\n");
		log("        slight increase in compilation time.\n");
		log("\n");
		log("    -O <level>\n");
		log("        set the optimization level. the default is -O%d. higher optimization\n", DEFAULT_OPT_LEVEL);
		log("        levels dramatically decrease compile and run time, and highest level\n");
		log("        possible for a design should be used.\n");
		log("\n");
		log("    -O0\n");
		log("        no optimization.\n");
		log("\n");
		log("    -O1\n");
		log("        unbuffer internal wires if possible.\n");
		log("\n");
		log("    -O2\n");
		log("        like -O1, and localize internal wires if possible.\n");
		log("\n");
		log("    -O3\n");
		log("        like -O2, and inline internal wires if possible.\n");
		log("\n");
		log("    -O4\n");
		log("        like -O3, and unbuffer public wires not marked (*keep*) if possible.\n");
		log("\n");
		log("    -O5\n");
		log("        like -O4, and localize public wires not marked (*keep*) if possible.\n");
		log("\n");
		log("    -O6\n");
		log("        like -O5, and inline public wires not marked (*keep*) if possible.\n");
		log("\n");
		log("    -g <level>\n");
		log("        set the debug level. the default is -g%d. higher debug levels provide\n", DEFAULT_DEBUG_LEVEL);
		log("        more visibility and generate more code, but do not pessimize evaluation.\n");
		log("\n");
		log("    -g0\n");
		log("        no debug information. the C API is disabled.\n");
		log("\n");
		log("    -g1\n");
		log("        include bare minimum of debug information necessary to access all design\n");
		log("        state. the C API is enabled.\n");
		log("\n");
		log("    -g2\n");
		log("        like -g1, but include debug information for all public wires that are\n");
		log("        directly accessible through the C++ interface.\n");
		log("\n");
		log("    -g3\n");
		log("        like -g2, and include debug information for public wires that are tied\n");
		log("        to a constant or another public wire.\n");
		log("\n");
		log("    -g4\n");
		log("        like -g3, and compute debug information on demand for all public wires\n");
		log("        that were optimized out.\n");
		log("\n");
	}

	void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design) override
	{
		bool print_wire_types = false;
		bool print_debug_wire_types = false;
		bool nohierarchy = false;
		bool noflatten = false;
		bool noproc = false;
		int opt_level = DEFAULT_OPT_LEVEL;
		int debug_level = DEFAULT_DEBUG_LEVEL;
		CxxrtlWorker worker;

		log_header(design, "Executing CXXRTL backend.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-print-wire-types") {
				print_wire_types = true;
				continue;
			}
			if (args[argidx] == "-print-debug-wire-types") {
				print_debug_wire_types = true;
				continue;
			}
			if (args[argidx] == "-nohierarchy") {
				nohierarchy = true;
				continue;
			}
			if (args[argidx] == "-noflatten") {
				noflatten = true;
				continue;
			}
			if (args[argidx] == "-noproc") {
				noproc = true;
				continue;
			}
			if (args[argidx] == "-Og") {
				log_warning("The `-Og` option has been removed. Use `-g3` instead for complete "
				            "design coverage regardless of optimization level.\n");
				continue;
			}
			if (args[argidx] == "-O" && argidx+1 < args.size() && args[argidx+1] == "g") {
				argidx++;
				log_warning("The `-Og` option has been removed. Use `-g3` instead for complete "
				            "design coverage regardless of optimization level.\n");
				continue;
			}
			if (args[argidx] == "-O" && argidx+1 < args.size()) {
				opt_level = std::stoi(args[++argidx]);
				continue;
			}
			if (args[argidx].substr(0, 2) == "-O" && args[argidx].size() == 3 && isdigit(args[argidx][2])) {
				opt_level = std::stoi(args[argidx].substr(2));
				continue;
			}
			if (args[argidx] == "-g" && argidx+1 < args.size()) {
				debug_level = std::stoi(args[++argidx]);
				continue;
			}
			if (args[argidx].substr(0, 2) == "-g" && args[argidx].size() == 3 && isdigit(args[argidx][2])) {
				debug_level = std::stoi(args[argidx].substr(2));
				continue;
			}
			if (args[argidx] == "-header") {
				worker.split_intf = true;
				continue;
			}
			if (args[argidx] == "-namespace" && argidx+1 < args.size()) {
				worker.design_ns = args[++argidx];
				continue;
			}
			break;
		}
		extra_args(f, filename, args, argidx);

		worker.print_wire_types = print_wire_types;
		worker.print_debug_wire_types = print_debug_wire_types;
		worker.run_hierarchy = !nohierarchy;
		worker.run_flatten = !noflatten;
		worker.run_proc = !noproc;
		switch (opt_level) {
			// the highest level here must match DEFAULT_OPT_LEVEL
			case 6:
				worker.inline_public = true;
				YS_FALLTHROUGH
			case 5:
				worker.localize_public = true;
				YS_FALLTHROUGH
			case 4:
				worker.unbuffer_public = true;
				YS_FALLTHROUGH
			case 3:
				worker.inline_internal = true;
				YS_FALLTHROUGH
			case 2:
				worker.localize_internal = true;
				YS_FALLTHROUGH
			case 1:
				worker.unbuffer_internal = true;
				YS_FALLTHROUGH
			case 0:
				break;
			default:
				log_cmd_error("Invalid optimization level %d.\n", opt_level);
		}
		switch (debug_level) {
			// the highest level here must match DEFAULT_DEBUG_LEVEL
			case 4:
				worker.debug_eval = true;
				YS_FALLTHROUGH
			case 3:
				worker.debug_alias = true;
				YS_FALLTHROUGH
			case 2:
				worker.debug_member = true;
				YS_FALLTHROUGH
			case 1:
				worker.debug_info = true;
				YS_FALLTHROUGH
			case 0:
				break;
			default:
				log_cmd_error("Invalid debug information level %d.\n", debug_level);
		}

		std::ofstream intf_f;
		if (worker.split_intf) {
			if (filename == "<stdout>")
				log_cmd_error("Option -header must be used with a filename.\n");

			worker.intf_filename = filename.substr(0, filename.rfind('.')) + ".h";
			intf_f.open(worker.intf_filename, std::ofstream::trunc);
			if (intf_f.fail())
				log_cmd_error("Can't open file `%s' for writing: %s\n",
				              worker.intf_filename.c_str(), strerror(errno));

			worker.intf_f = &intf_f;
		}
		worker.impl_f = f;

		worker.prepare_design(design);
		worker.dump_design(design);
	}
} CxxrtlBackend;

PRIVATE_NAMESPACE_END
