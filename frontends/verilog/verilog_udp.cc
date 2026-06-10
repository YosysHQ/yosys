/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2026  Remy Goldschmidt <taktoa@gmail.com>
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
 *  ---
 *
 *  Lowering of Verilog user-defined primitives (UDPs, IEEE 1364-2005 clause 8)
 *  into ordinary Yosys netlists.
 *
 *  A UDP is an event-driven, four-valued state machine: on every change of an
 *  input it re-evaluates its state table using the new input values, the
 *  *previous* input values (to recognise transitions), and the current output
 *  state.  We reproduce exactly that behaviour with a small netlist:
 *
 *      assign out = G(in, prev_in, state);   // combinational table evaluation
 *      prev_in <= in;                         // $ff: previous input vector
 *      state   <= out;                        // $ff: previous output / state
 *
 *  The two registers are `$ff` cells (formal/simulation flip-flops with an
 *  implicit global clock that advances once per simulation event).  Because
 *  `out` is purely combinational it reflects the result of the current event
 *  immediately, while the registers lag by one event and therefore hold the
 *  "previous" values that the next evaluation needs.  Under `yosys sim` (which
 *  advances the global clock once per input change) this matches Icarus
 *  Verilog's native UDP simulation bit-for-bit, including all x behaviour.
 *
 *  The table is matched with case-equality (`$eqx`/`$nex`) so that the four
 *  values 0/1/x are distinguished exactly; z inputs are treated as x by the
 *  surrounding logic just as the standard requires.
 */

#include "frontends/verilog/verilog_udp.h"
#include "frontends/verilog/verilog_frontend.h"
#include "kernel/log.h"

YOSYS_NAMESPACE_BEGIN
using namespace AST;

namespace VERILOG_FRONTEND {

namespace {

using ast_t = std::unique_ptr<AstNode>;

struct UdpLower {
	UdpParseData &udp;
	AstSrcLocType loc;

	int n_in = 0;
	std::vector<std::string> in_names;	// input port names, header order
	std::vector<std::string> sig_names;	// z->x mapped input signals (used for matching)
	std::string out_name;

	AstNode *mod = nullptr;			// module being built (for adding wires/cells)
	AstNode *out_wire = nullptr;
	int autoidx = 0;

	UdpLower(UdpParseData &udp) : udp(udp), loc(udp.loc) {}

	[[noreturn]] void error(const std::string &msg)
	{
		std::string fn = loc.begin.filename ? *loc.begin.filename : std::string("<unknown>");
		const char *nm = udp.name.empty() ? "" : udp.name.c_str() + (udp.name[0] == '\\' ? 1 : 0);
		log_file_error(fn, loc.begin.line, "UDP `%s': %s\n", nm, msg.c_str());
	}

	// --- tiny AST builders ---------------------------------------------------
	ast_t N(AstNodeType t) { return std::make_unique<AstNode>(loc, t); }
	ast_t N(AstNodeType t, ast_t a) { return std::make_unique<AstNode>(loc, t, std::move(a)); }
	ast_t N(AstNodeType t, ast_t a, ast_t b) { return std::make_unique<AstNode>(loc, t, std::move(a), std::move(b)); }
	ast_t N(AstNodeType t, ast_t a, ast_t b, ast_t c) { return std::make_unique<AstNode>(loc, t, std::move(a), std::move(b), std::move(c)); }

	ast_t mk_id(const std::string &name) { auto n = N(AST_IDENTIFIER); n->str = name; return n; }
	ast_t mk_const(RTLIL::State s) { return AstNode::mkconst_bits(loc, std::vector<RTLIL::State>{s}, false); }

	ast_t mk_and(ast_t a, ast_t b)
	{
		if (!a) return b;
		if (!b) return a;
		return N(AST_BIT_AND, std::move(a), std::move(b));
	}
	ast_t mk_or(ast_t a, ast_t b)
	{
		if (!a) return b;
		if (!b) return a;
		return N(AST_BIT_OR, std::move(a), std::move(b));
	}
	// case-equality: (sig === value), always a definite 0/1
	ast_t mk_eqx(ast_t sig, RTLIL::State value) { return N(AST_EQX, std::move(sig), mk_const(value)); }
	// case-inequality of two one-bit signals: (a !== b)
	ast_t mk_nex(ast_t a, ast_t b) { return N(AST_NEX, std::move(a), std::move(b)); }

	// --- symbol helpers ------------------------------------------------------
	// One-bit expression that is true iff `sig` matches the level symbol.
	// Returns null for the unconstrained symbols '?' (and 'b' is expanded).
	ast_t level_match(char sym, ast_t sig)
	{
		switch (tolower(sym)) {
		case '0': return mk_eqx(std::move(sig), RTLIL::State::S0);
		case '1': return mk_eqx(std::move(sig), RTLIL::State::S1);
		case 'x': return mk_eqx(std::move(sig), RTLIL::State::Sx);
		case '?': return nullptr; // matches anything
		case 'b': {
			// 0 or 1 (not x)
			auto a = mk_eqx(sig->clone(), RTLIL::State::S0);
			auto b = mk_eqx(std::move(sig), RTLIL::State::S1);
			return mk_or(std::move(a), std::move(b));
		}
		default:
			error(stringf("unexpected level symbol `%c' in table", sym));
		}
	}

	static bool is_edge_symbol(const std::string &s)
	{
		if (s.size() >= 1 && s.front() == '(')
			return true;
		if (s.size() == 1) {
			char c = tolower(s[0]);
			return c == 'r' || c == 'f' || c == 'p' || c == 'n' || c == '*';
		}
		return false;
	}

	// One-bit expression that is true iff the transition (piv -> in) matches the
	// edge symbol.  Both operands are one-bit signals.
	ast_t edge_match(const std::string &sym, const std::string &piv, const std::string &in)
	{
		std::vector<std::pair<char, char>> pairs;
		if (!sym.empty() && sym.front() == '(') {
			if (sym.size() != 4 || sym.back() != ')')
				error(stringf("malformed edge specifier `%s' in table", sym.c_str()));
			pairs.emplace_back(sym[1], sym[2]);
		} else {
			switch (tolower(sym[0])) {
			case '*': pairs.emplace_back('?', '?'); break;
			case 'r': pairs.emplace_back('0', '1'); break;
			case 'f': pairs.emplace_back('1', '0'); break;
			case 'p': pairs = {{'0','1'},{'0','x'},{'x','1'}}; break;
			case 'n': pairs = {{'1','0'},{'1','x'},{'x','0'}}; break;
			default: error(stringf("unexpected edge symbol `%s' in table", sym.c_str()));
			}
		}
		ast_t acc;
		for (auto &p : pairs) {
			ast_t m = mk_and(level_match(p.first, mk_id(piv)), level_match(p.second, mk_id(in)));
			// an edge is always a change of value
			m = mk_and(std::move(m), mk_nex(mk_id(piv), mk_id(in)));
			acc = mk_or(std::move(acc), std::move(m));
		}
		return acc;
	}

	// --- row matching --------------------------------------------------------
	// `piv_names` is empty for a combinational table (no edges, no previous
	// inputs).  `state_name` is empty for a combinational table.
	ast_t row_match(const UdpTableRow &row, const std::vector<std::string> &piv_names,
			const std::string &state_name)
	{
		ast_t acc;
		int edge_count = 0;
		for (int i = 0; i < n_in; i++) {
			const std::string &sym = row.inputs[i];
			if (is_edge_symbol(sym)) {
				if (piv_names.empty())
					error("input transitions are only allowed in sequential UDPs");
				if (++edge_count > 1)
					error("a UDP table row may contain at most one input transition");
				acc = mk_and(std::move(acc), edge_match(sym, piv_names[i], sig_names[i]));
			} else {
				acc = mk_and(std::move(acc), level_match(sym[0], mk_id(sig_names[i])));
			}
		}
		if (!row.current.empty()) {
			if (is_edge_symbol(row.current))
				error("the current-state field of a UDP row must be a level");
			acc = mk_and(std::move(acc), level_match(row.current[0], mk_id(state_name)));
		}
		return acc; // null means "matches unconditionally"
	}

	bool row_has_edge(const UdpTableRow &row)
	{
		for (auto &sym : row.inputs)
			if (is_edge_symbol(sym))
				return true;
		return false;
	}

	char row_output(const UdpTableRow &row)
	{
		char c = row.output.empty() ? '?' : tolower(row.output[0]);
		if (c != '0' && c != '1' && c != 'x' && c != '-')
			error(stringf("unexpected output symbol `%s' in table", row.output.c_str()));
		return c;
	}

	// --- determinism check ---------------------------------------------------
	// The set of values {0,1,x} (bits 0,1,2) a level symbol can match.
	static unsigned level_set(char c)
	{
		switch (tolower(c)) {
		case '0': return 1;
		case '1': return 2;
		case 'x': return 4;
		case 'b': return 3;
		case '?': return 7;
		default:  return 7; // empty current-state field: unconstrained
		}
	}

	static std::vector<std::pair<char, char>> edge_pairs(const std::string &s)
	{
		if (!s.empty() && s.front() == '(')
			return {{s[1], s[2]}};
		switch (tolower(s.empty() ? '?' : s[0])) {
		case '*': return {{'?', '?'}};
		case 'r': return {{'0', '1'}};
		case 'f': return {{'1', '0'}};
		case 'p': return {{'0','1'},{'0','x'},{'x','1'}};
		case 'n': return {{'1','0'},{'1','x'},{'x','0'}};
		}
		return {};
	}

	// The set of (from,to) transitions an edge symbol can match, encoded as a
	// bitmask over from*3+to (with from != to).
	static unsigned edge_set(const std::string &s)
	{
		unsigned m = 0;
		for (auto &p : edge_pairs(s)) {
			unsigned fs = level_set(p.first), ts = level_set(p.second);
			for (int f = 0; f < 3; f++)
				for (int t = 0; t < 3; t++)
					if ((fs >> f & 1) && (ts >> t & 1) && f != t)
						m |= 1u << (f * 3 + t);
		}
		return m;
	}

	int edge_pos(const UdpTableRow &row)
	{
		int pos = -1;
		for (int i = 0; i < n_in; i++)
			if (is_edge_symbol(row.inputs[i])) {
				if (pos >= 0) {
					loc = row.loc;
					error("a UDP table row may contain at most one input transition");
				}
				pos = i;
			}
		return pos;
	}

	// Reject tables whose behaviour is not uniquely determined: two rows that
	// can match the same evaluation (same input values / transition and current
	// state) but specify different definite outputs.  `x` outputs are
	// don't-cares and never conflict; level-sensitive rows are allowed to
	// override edge-sensitive rows (IEEE 1364-2005 8.7), so only same-kind rows
	// are compared.
	void check_determinism()
	{
		for (size_t a = 0; a < udp.rows.size(); a++)
		for (size_t b = a + 1; b < udp.rows.size(); b++) {
			const UdpTableRow &A = udp.rows[a], &B = udp.rows[b];
			char oa = row_output(A), ob = row_output(B);
			if (oa == ob || oa == 'x' || ob == 'x')
				continue;
			int ea = edge_pos(A), eb = edge_pos(B);
			if (ea != eb)
				continue; // level-vs-edge (defined), or edges on different inputs
			bool overlap = true;
			for (int i = 0; i < n_in && overlap; i++) {
				if (i == ea)
					overlap = (edge_set(A.inputs[i]) & edge_set(B.inputs[i])) != 0;
				else
					overlap = (level_set(A.inputs[i][0]) & level_set(B.inputs[i][0])) != 0;
			}
			if (overlap && !A.current.empty() && !B.current.empty())
				overlap = (level_set(A.current[0]) & level_set(B.current[0])) != 0;
			if (overlap) {
				loc = A.loc;
				error(stringf("non-deterministic state table: the rows at lines %d and %d "
					      "match the same input combination but specify different "
					      "outputs (`%c' and `%c')",
					      A.loc.begin.line, B.loc.begin.line, oa, ob));
			}
		}
	}

	// OR of the match expressions of all rows whose output symbol is `want`.
	// Returns null for an empty bucket.  Matches Icarus Verilog, which groups
	// table rows by output value rather than by table order.
	ast_t bucket_match(const std::vector<const UdpTableRow*> &rows, char want,
			   const std::vector<std::string> &piv_names, const std::string &state_name)
	{
		ast_t acc;
		for (auto *row : rows) {
			if (row_output(*row) != want)
				continue;
			ast_t m = row_match(*row, piv_names, state_name);
			if (!m)
				m = AstNode::mkconst_int(loc, 1, false, 1); // unconditional match
			acc = mk_or(std::move(acc), std::move(m));
		}
		return acc;
	}

	// `cond ? then_expr : else_expr`, dropping the choice when the bucket is
	// empty (cond is null).
	ast_t sel(ast_t cond, ast_t then_expr, ast_t else_expr)
	{
		if (!cond)
			return else_expr;
		return N(AST_TERNARY, std::move(cond), std::move(then_expr), std::move(else_expr));
	}

	// --- netlist construction helpers ---------------------------------------
	AstNode *add_wire(const std::string &name, bool is_input, bool is_output, int port_id)
	{
		auto w = N(AST_WIRE);
		w->str = name;
		w->is_input = is_input;
		w->is_output = is_output;
		if (port_id)
			w->port_id = port_id;
		AstNode *ptr = w.get();
		mod->children.push_back(std::move(w));
		return ptr;
	}

	// A $ff (implicit global clock flip-flop): q <= d on every simulation event.
	void add_ff(ast_t d_expr, const std::string &q_name, bool have_init, RTLIL::State init)
	{
		AstNode *q = add_wire(q_name, false, false, 0);
		if (have_init)
			q->set_attribute(ID::init, AstNode::mkconst_bits(loc, std::vector<RTLIL::State>{init}, false));

		auto cell = N(AST_CELL);
		cell->str = stringf("$udp$ff$%d", autoidx++);
		auto celltype = N(AST_CELLTYPE);
		celltype->str = "$ff";
		cell->children.push_back(std::move(celltype));

		auto para = N(AST_PARASET);
		para->str = "\\WIDTH";
		para->children.push_back(AstNode::mkconst_int(loc, 1, false, 32));
		cell->children.push_back(std::move(para));

		auto arg_d = N(AST_ARGUMENT);
		arg_d->str = "\\D";
		arg_d->children.push_back(std::move(d_expr));
		cell->children.push_back(std::move(arg_d));

		auto arg_q = N(AST_ARGUMENT);
		arg_q->str = "\\Q";
		arg_q->children.push_back(mk_id(q_name));
		cell->children.push_back(std::move(arg_q));

		mod->children.push_back(std::move(cell));
	}

	// --- entry point ---------------------------------------------------------
	std::unique_ptr<AstNode> run()
	{
		// Resolve and validate ports.
		if (udp.port_order.size() < 2)
			error("a UDP must have an output and at least one input");
		if (!udp.output_declared)
			error("missing output port declaration");
		out_name = udp.output_name;
		if (udp.port_order[0] != out_name)
			error("the output port must be the first port in the port list");
		for (size_t i = 1; i < udp.port_order.size(); i++) {
			if (!udp.input_names.count(udp.port_order[i]))
				error(stringf("port `%s' is missing an input declaration",
					udp.port_order[i].c_str() + 1));
			in_names.push_back(udp.port_order[i]);
		}
		n_in = GetSize(in_names);

		for (auto &row : udp.rows) {
			if (GetSize(row.inputs) != n_in) {
				loc = row.loc;
				error(stringf("table row has %d input fields but the UDP has %d inputs",
					GetSize(row.inputs), n_in));
			}
		}
		if (udp.is_sequential && !udp.table_is_sequential)
			error("sequential UDP has a combinational state table");
		if (!udp.is_sequential && udp.table_is_sequential)
			error("combinational UDP has a sequential state table");
		if (udp.rows.empty())
			error("empty state table");

		check_determinism();
		loc = udp.loc;

		// Build the module skeleton.
		auto module = N(AST_MODULE);
		module->str = udp.name;
		if (udp.attributes)
			for (auto &it : *udp.attributes)
				module->attributes[it.first] = std::move(it.second);
		module->set_attribute(ID(udp), AstNode::mkconst_int(loc, 1, false));
		mod = module.get();

		int port_id = 1;
		out_wire = add_wire(out_name, false, true, port_id++);
		for (auto &in : in_names)
			add_wire(in, true, false, port_id++);

		// "The z values passed to UDP inputs shall be treated the same as x
		// values."  Map each input through (in === 1'bz) ? 1'bx : in and use the
		// mapped signal everywhere the table is matched.  (The constants also
		// force these cells to be evaluated in the first simulation step.)
		for (int i = 0; i < n_in; i++) {
			std::string xn = stringf("$udp$zx%d", i);
			add_wire(xn, false, false, 0);
			ast_t map = N(AST_TERNARY,
				mk_eqx(mk_id(in_names[i]), RTLIL::State::Sz),
				mk_const(RTLIL::State::Sx), mk_id(in_names[i]));
			mod->children.push_back(N(AST_ASSIGN, mk_id(xn), std::move(map)));
			sig_names.push_back(xn);
		}

		if (!udp.is_sequential)
			build_combinational();
		else
			build_sequential();

		mod = nullptr;
		return module;
	}

	void build_combinational()
	{
		// out = 0 if any 0-row matches, else 1 if any 1-row matches, else x.
		// (x-output rows do not force x; they simply are not 0- or 1-rows.)
		std::vector<const UdpTableRow*> rows;
		for (auto &row : udp.rows) {
			if (row_has_edge(row))
				error("combinational UDPs may not contain input transitions");
			if (row_output(row) == '-')
				error("`-' (no change) is only allowed in sequential UDPs");
			rows.push_back(&row);
		}
		ast_t expr = sel(bucket_match(rows, '0', {}, ""), mk_const(RTLIL::State::S0),
				 sel(bucket_match(rows, '1', {}, ""), mk_const(RTLIL::State::S1),
				     mk_const(RTLIL::State::Sx)));
		mod->children.push_back(N(AST_ASSIGN, mk_id(out_name), std::move(expr)));
	}

	void build_sequential()
	{
		// State registers: one $ff per input for the previous input value, plus
		// one $ff for the previous output (the current state).
		std::vector<std::string> piv_names;
		for (int i = 0; i < n_in; i++)
			piv_names.push_back(stringf("$udp$piv%d", i));
		std::string state_name = "$udp$state";

		// out = G(in, prev_in, state):
		//   level rows (priority) override edge rows (priority); if nothing
		//   matches, hold the state when no input changed, else x.
		std::vector<const UdpTableRow*> level_rows, edge_rows;
		for (auto &row : udp.rows) {
			if (row_has_edge(row))
				edge_rows.push_back(&row);
			else
				level_rows.push_back(&row);
		}

		// A UDP only re-evaluates its table when one of its inputs *changes*;
		// otherwise the output holds.  So:
		//   out = event ? table(in, prev_in, state) : state
		// where event = (in !== prev_in).  The constant bit padded onto each
		// side forces this comparison (and hence the whole output) to be
		// evaluated in the very first simulation step, when all inputs are still
		// x and would otherwise never be re-evaluated; there the event is false,
		// so the output correctly holds the initial state.
		auto in_concat = N(AST_CONCAT);
		auto piv_concat = N(AST_CONCAT);
		for (int i = 0; i < n_in; i++) {
			in_concat->children.push_back(mk_id(sig_names[i]));
			piv_concat->children.push_back(mk_id(piv_names[i]));
		}
		in_concat->children.push_back(mk_const(RTLIL::State::S0));
		piv_concat->children.push_back(mk_const(RTLIL::State::S0));
		ast_t event = N(AST_NEX, std::move(in_concat), std::move(piv_concat));

		// table(): rows are tried by output value in a fixed priority that
		// matches Icarus Verilog's evaluator (vvp/udp.cc):
		//   level 0 > level 1 > level x > level hold > edge 0 > edge 1 > edge hold > x
		// Level entries dominate edge entries; an edge entry on an input that did
		// not transition cannot match (handled inside the per-row match).
		auto S = [&](RTLIL::State s) { return mk_const(s); };
		auto St = [&]() { return mk_id(state_name); };
		ast_t table =
		  sel(bucket_match(level_rows, '0', piv_names, state_name), S(RTLIL::State::S0),
		  sel(bucket_match(level_rows, '1', piv_names, state_name), S(RTLIL::State::S1),
		  sel(bucket_match(level_rows, 'x', piv_names, state_name), S(RTLIL::State::Sx),
		  sel(bucket_match(level_rows, '-', piv_names, state_name), St(),
		  sel(bucket_match(edge_rows,  '0', piv_names, state_name), S(RTLIL::State::S0),
		  sel(bucket_match(edge_rows,  '1', piv_names, state_name), S(RTLIL::State::S1),
		  sel(bucket_match(edge_rows,  '-', piv_names, state_name), St(),
		      S(RTLIL::State::Sx))))))));
		ast_t out_expr = N(AST_TERNARY, std::move(event), std::move(table), mk_id(state_name));
		mod->children.push_back(N(AST_ASSIGN, mk_id(out_name), std::move(out_expr)));

		// The output is combinational; also give it the initial value so the
		// very first sampled output is correct even before it is evaluated.
		RTLIL::State init = udp_init_state();
		out_wire->set_attribute(ID::init, AstNode::mkconst_bits(loc, std::vector<RTLIL::State>{init}, false));

		// previous-input registers (store the z->x mapped values)
		for (int i = 0; i < n_in; i++)
			add_ff(mk_id(sig_names[i]), piv_names[i], /*have_init=*/true, RTLIL::State::Sx);

		// state register (previous output)
		add_ff(mk_id(out_name), state_name, /*have_init=*/true, init);
	}

	// Reduce the UDP's initial-value expression to a single 4-state bit.
	// `initial q = <init_val>;` is restricted by the standard to 1'b0, 1'b1,
	// 1'bx, 1, or 0, all of which the front-end parses to an AST_CONSTANT.
	RTLIL::State udp_init_state()
	{
		if (!udp.initial_val)
			return RTLIL::State::Sx;
		AstNode *e = udp.initial_val.get();
		if (e->type != AST_CONSTANT || e->bits.empty())
			error("initial value must be a constant 1'b0, 1'b1 or 1'bx");
		return e->bits.front();
	}
};

} // anonymous namespace

std::unique_ptr<AstNode> make_udp_module(UdpParseData &udp)
{
	UdpLower lower(udp);
	return lower.run();
}

} // namespace VERILOG_FRONTEND

YOSYS_NAMESPACE_END
