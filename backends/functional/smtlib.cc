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

#include "kernel/yosys.h"
#include "kernel/drivertools.h"
#include "kernel/topo_scc.h"
#include "kernel/functional.h"
#include "kernel/graphtools.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct SmtlibScope {
	pool<std::string> used_names;
	dict<IdString, std::string> name_map;

	SmtlibScope() {
		/*for(const char **p = reserved_keywords; *p != nullptr; p++)
			reserve(*p);*/
	}
	void reserve(std::string name) {
		used_names.insert(name);
	}
	std::string insert(IdString id) {
		std::string str = RTLIL::unescape_id(id);
		for(size_t i = 0; i < str.size(); i++)
			if(!((unsigned char)str[i] < 0x80 && (isalnum(str[i]) || strchr("~!@$%^&*_-+=<>.?/", str[i]))))
				str[i] = '_';
		if(used_names.count(str) == 0){
			used_names.insert(str);
			name_map.insert({id, str});
			return str;
		}
		for (int idx = 0 ; ; idx++){
			std::string suffixed = str + "_" + std::to_string(idx);
			if (used_names.count(suffixed) == 0) {
				used_names.insert(suffixed);
				if(name_map.count(id) == 0)
					name_map.insert({id, suffixed});
				return suffixed;
			}
		}
	}
	std::string operator[](IdString id) {
		if(name_map.count(id) > 0)
			return name_map[id];
		else
			return insert(id);
	}
};

struct SmtlibWriter {
	std::ostream &f;
	SmtlibWriter(std::ostream &out) : f(out) {}
	void printf(const char *fmt, ...)
	{
		va_list va;
		va_start(va, fmt);
		f << vstringf(fmt, va);
		va_end(va);
	}
	template <typename T>
	SmtlibWriter & operator <<(T &&arg) {
		f << std::forward<T>(arg);
		return *this;
	}
};

struct Arg {
    int n;
    explicit Arg(int n_) : n(n_) {}
	bool operator ==(Arg const &other) const { return n == other.n; }
};

class SExpr {
	enum class Type {
		None,
		List,
		Atom,
		Arg,
	};
	Type type = Type::None;
	union {
		std::string atom_;
		vector<SExpr> list_;
        Arg arg_;
	};
    void set_none() {
        switch(type) {
        case Type::None: break;
        case Type::Atom: atom_.~basic_string(); break;
        case Type::List: list_.~vector(); break;
        case Type::Arg: arg_.~Arg(); break;
        }
        type = Type::None;
    }
public:
	SExpr() {}
    SExpr(const char *atom) : type(Type::Atom), atom_(atom) {}
	SExpr(std::string atom) : type(Type::Atom), atom_(atom) {}
	SExpr(int n) : type(Type::Atom), atom_(std::to_string(n)) {}
	SExpr(RTLIL::Const const & n) : type(Type::Atom) {
		new(&atom_) std::string("#b");
		atom_.reserve(n.size() + 2);
		for (size_t i = n.size(); i > 0; i--)
			if(n[i-1] == State::S1)
				atom_ += "1";
			else
				atom_ += "0";
	}
	SExpr(vector<SExpr> &&list) : type(Type::List), list_(list) {}
    SExpr(std::initializer_list<SExpr> list) : type(Type::List), list_(list) {}
    SExpr(Arg arg) : type(Type::Arg), arg_(arg) {}
    SExpr(SExpr const &other) { *this = other; }
    SExpr(SExpr &&other) { *this = std::move(other); }
    SExpr &operator =(SExpr const &other) {
        set_none();
        switch(other.type) {
        case Type::None: break;
        case Type::Atom: new(&atom_) std::string(other.atom_); break;
        case Type::List: new(&list_) vector<SExpr>(other.list_); break;
        case Type::Arg: new(&arg_) Arg(other.arg_); break;
        }
        type = other.type;
        return *this;
    }
    SExpr &operator =(SExpr &&other) {
        set_none();
        switch(other.type) {
        case Type::None: break;
        case Type::Atom: new(&atom_) std::string(std::move(other.atom_)); break;
        case Type::List: new(&list_) vector<SExpr>(std::move(other.list_)); break;
        case Type::Arg: new(&arg_) Arg(std::move(other.arg_)); break;
        }
        type = other.type;
        return *this;
    }
    ~SExpr() { set_none(); }
	bool operator==(SExpr const &other) const {
		if(type != other.type) return false;
		switch(type) {
		case Type::None: return true;
		case Type::Atom: return atom_ == other.atom_;
		case Type::List: return list_ == other.list_;
		case Type::Arg: return arg_ == other.arg_;
		}
	}
    bool is_none() const { return type == Type::None; }
	bool is_atom() const { return type == Type::Atom; }
	bool is_list() const { return type == Type::List; }
    bool is_arg() const { return type == Type::Arg; }
    std::string const &atom() const { log_assert(is_atom()); return atom_; }
    std::vector<SExpr> const &list() const { log_assert(is_list()); return list_; }
    Arg const &arg() const { log_assert(is_arg()); return arg_; }
	unsigned int hash() const {
		unsigned int inner;
		switch(type) {
		case Type::None: inner = 0; break;
		case Type::Atom: inner = mkhash(atom_); break;
		case Type::List: inner = mkhash(list_); break;
		case Type::Arg: inner = arg_.n; break;
		}
		return mkhash((unsigned int) type, inner);
	}
	SExpr subst_args(std::vector<SExpr> const & args) const {
		switch(type) {
		case Type::None:
		case Type::Atom:
			return *this;
		case Type::List: {
			vector<SExpr> ret;
			for(auto & a : list_)
				ret.emplace_back(a.subst_args(args));
			return SExpr(std::move(ret));
		}
		case Type::Arg:
			if(arg_.n >= 1 && (size_t)arg_.n <= args.size())
				return args[arg_.n - 1];
			else
				return *this;
		}
	}
};

std::ostream& operator << (std::ostream &os, SExpr const &s) {
    if(s.is_atom())
        os << s.atom();
    else if(s.is_list()){
        os << "(";
        bool first = true;
        for(auto &el: s.list()) {
            if(!first) os << " ";
            else first = false;
            os << el;
        }
        os << ")";
    }else if(s.is_arg())
        os << "#" << s.arg().n;
    else if(s.is_none())
        os << "<none>";
    else
        os << "???";
    return os;
}

struct SmtlibType {
	bool _is_memory;
	int _width;
	int _addr_width;
public:
	SmtlibType() : _is_memory(false), _width(0), _addr_width(0) { }
	SmtlibType(int width) : _is_memory(false), _width(width), _addr_width(0) { }
	SmtlibType(int addr_width, int data_width) : _is_memory(true), _width(data_width), _addr_width(addr_width) { }
	static SmtlibType signal(int width) { return SmtlibType(width); }
	static SmtlibType memory(int addr_width, int data_width) { return SmtlibType(addr_width, data_width); }
	bool is_signal() const { return !_is_memory; }
	bool is_memory() const { return _is_memory; }
	int width() const { log_assert(is_signal()); return _width; }
	int addr_width() const { log_assert(is_memory()); return _addr_width; }
	int data_width() const { log_assert(is_memory()); return _width; }
	SExpr to_sexpr() const {
		if(_is_memory) {
			return SExpr{ "Array", SExpr{ "_", "BitVec", addr_width() }, SExpr{ "_", "BitVec", data_width() }};
		} else {
			return SExpr{ "_", "BitVec", width() };
		}
	}
	bool operator ==(SmtlibType const& other) const {
		if(_is_memory != other._is_memory) return false;
		if(_is_memory && _addr_width != other._addr_width) return false;
		return _width == other._width;
	}
	unsigned int hash() const {
		if(_is_memory)
			return mkhash(1, mkhash(_width, _addr_width));
		else
			return mkhash(0, _width);
	}
};

struct SmtlibStruct {
	SmtlibScope &scope;
	std::string name;
	idict<IdString> members;
	vector<SmtlibType> types;
	vector<std::string> accessors;
	SmtlibStruct(std::string name, SmtlibScope &scope) : scope(scope), name(name) {
	}
	std::string insert(IdString field, SmtlibType type) {
		if(members.at(field, -1) == -1){
			members(field);
			scope.insert(field);
			types.push_back(type);
			accessors.push_back(scope.insert(std::string("\\") + name + "_" + RTLIL::unescape_id(field)));
		}
		return scope[field];
	}
	void print(SmtlibWriter &f) {
		f.printf("(declare-datatype %s ((%s\n", name.c_str(), name.c_str());
		for (size_t i = 0; i < members.size(); i++)
			f << "  " << SExpr{accessors[i], types[i].to_sexpr()} << "\n";
		f.printf(")))\n");
	}
	void print_value(SmtlibWriter &f, dict<IdString, SExpr> values, int indentation) {
		std::string spaces(indentation, ' ');
		f << spaces << "(" << name << "\n";
		for (size_t i = 0; i < members.size(); i++)
			f << spaces << "  " << values[members[i]] << "    ; " << RTLIL::unescape_id(members[i]) << "\n";
		f << spaces << ")\n";
	}
	SExpr access(SExpr record, IdString member) {
		int i = members.at(member);
		return SExpr{accessors[i], record};
	}
	std::string operator[](IdString field) {
		return scope[field];
	}
};

struct Node {
	SExpr expr;
	SmtlibType type;

	Node(SExpr &&expr, SmtlibType type) : expr(std::move(expr)), type(type) {}

	bool operator==(Node const &other) const {
		return expr == other.expr && type == other.type;
	}

	unsigned int hash() const {
		return mkhash(expr.hash(), type.hash());
	}
};

typedef ComputeGraph<Node, int, IdString, IdString> SmtlibComputeGraph;

struct SmtlibModule {
	std::string name;
	SmtlibScope global_scope;
	SmtlibStruct input_struct;
	SmtlibStruct output_struct;
	SmtlibStruct state_struct;
	SmtlibComputeGraph compute_graph;

	SmtlibModule(std::string const &name) :
		name(name),
		input_struct(name + "_inputs", global_scope),
		output_struct(name + "_outputs", global_scope),
		state_struct(name + "_state", global_scope)
	{ }
	void calculate_compute_graph(RTLIL::Module *module);
	void write(std::ostream &stream);
};

class SmtlibComputeGraphFactory {
	SmtlibModule &module;
	SmtlibComputeGraph &graph;
	using T = SmtlibComputeGraph::Ref;
	static bool is_single_output(IdString type)
	{
		auto it = yosys_celltypes.cell_types.find(type);
		return it != yosys_celltypes.cell_types.end() && it->second.outputs.size() <= 1;
	}
	T node(SExpr &&expr, SmtlibType type, std::initializer_list<T> args) {
		return graph.add(Node(std::move(expr), type), 0, args);
	}
	T shift(const char *name, T a, T b, int y_width, int b_width, bool a_signed = false) {
		int width = max(y_width, b_width);
		T a_ = y_width < width ? extend(a, y_width, width, a_signed) : a;
		T b_ = b_width < width ? extend(b, b_width, width, false) : b;
		T y_ = node(SExpr {name, Arg(1), Arg(2)}, width, {a_, b_});
		if(y_width < width)
			return slice(y_, width, 0, y_width);
		else
			return y_;
	}
	SExpr from_bool(SExpr &&arg) {
		return SExpr{"ite", std::move(arg), RTLIL::Const(State::S1), RTLIL::Const(State::S0)};
	}
	SExpr to_bool(SExpr &&arg) {
		return SExpr{"=", std::move(arg), RTLIL::Const(State::S1)};
	}
	SExpr extract(SExpr &&arg, int offset, int out_width) {
		return SExpr {SExpr {"_", "extract", offset + out_width - 1, offset}, std::move(arg)};
	}
public:
	SmtlibComputeGraphFactory(SmtlibModule &mod) : module(mod), graph(mod.compute_graph) {}
	T slice(T a, int in_width, int offset, int out_width) {
		log_assert(offset + out_width <= in_width);
		return node(extract(Arg(1), offset, out_width), out_width, {a});
	}
	T extend(T a, int in_width, int out_width, bool is_signed) {
		log_assert(in_width < out_width);
		if(is_signed)
			return node(SExpr {SExpr {"_", "sign_extend", out_width - in_width}, Arg(1)}, out_width, {a});
		else
			return node(SExpr {SExpr {"_", "zero_extend", out_width - in_width}, Arg(1)}, out_width, {a});
	}
	T concat(T a, int a_width, T b, int b_width) {
		return node(SExpr {"concat", Arg(1), Arg(2)}, a_width + b_width, {a, b});
	}
	T add(T a, T b, int width) { return node(SExpr {"bvadd", Arg(1), Arg(2)}, width, {a, b}); }
	T sub(T a, T b, int width) { return node(SExpr {"bvsub", Arg(1), Arg(2)}, width, {a, b}); }
	T bitwise_and(T a, T b, int width) { return node(SExpr {"bvand", Arg(1), Arg(2)}, width, {a, b}); }
	T bitwise_or(T a, T b, int width) { return node(SExpr {"bvor", Arg(1), Arg(2)}, width, {a, b}); }
	T bitwise_xor(T a, T b, int width) { return node(SExpr {"bvxor", Arg(1), Arg(2)}, width, {a, b}); }
	T bitwise_not(T a, int width) { return node(SExpr {"bvnot", Arg(1)}, width, {a}); }
	T neg(T a, int width) { return node(SExpr {"bvneg", Arg(1)}, width, {a}); }
	T mux(T a, T b, T s, int width) { return node(SExpr {"ite", to_bool(Arg(1)), Arg(2), Arg(3)}, width, {s, a, b}); }
	T pmux(T a, T b, T s, int width, int s_width) { 
		T rv = a;
		for(int i = 0; i < s_width; i++)
			rv = node(SExpr {"ite", to_bool(extract(Arg(1), i, 1)), extract(Arg(2), width * i, width), Arg(3)}, width, {s, b, rv});
		return rv;
	}
	T reduce_and(T a, int width) { return node(from_bool(SExpr {"=", Arg(1), RTLIL::Const(State::S1, width)}), 1, {a}); }
	T reduce_or(T a, int width) { return node(from_bool(SExpr {"distinct", Arg(1), RTLIL::Const(State::S0, width)}), 1, {a}); }
	T reduce_xor(T a, int) { return node(SExpr {"reduce_xor", Arg(1)}, 1, {a}); }
	T eq(T a, T b, int) { return node(from_bool(SExpr {"=", Arg(1), Arg(2)}), 1, {a, b}); }
	T ne(T a, T b, int) { return node(from_bool(SExpr {"distinct", Arg(1), Arg(2)}), 1, {a, b}); }
	T gt(T a, T b, int) { return node(from_bool(SExpr {"bvsgt", Arg(1), Arg(2)}), 1, {a, b}); }
	T ge(T a, T b, int) { return node(from_bool(SExpr {"bvsge", Arg(1), Arg(2)}), 1, {a, b}); }
	T ugt(T a, T b, int) { return node(from_bool(SExpr {"bvugt", Arg(1), Arg(2)}), 1, {a, b}); }
	T uge(T a, T b, int) { return node(from_bool(SExpr {"bvuge", Arg(1), Arg(2)}), 1, {a, b}); }
	T logical_shift_left(T a, T b, int y_width, int b_width) { return shift("bvshl", a, b, y_width, b_width); }
	T logical_shift_right(T a, T b, int y_width, int b_width) { return shift("bvlshl", a, b, y_width, b_width); }
	T arithmetic_shift_right(T a, T b, int y_width, int b_width) { return shift("bvashr", a, b, y_width, b_width, true); }

	T memory_read(T mem, T addr, int addr_width, int data_width) {
		return node(SExpr {"select", Arg(1), Arg(2)}, data_width, {mem, addr});
	}
	T memory_write(T mem, T addr, T data, int addr_width, int data_width) {
		return node(SExpr {"store", Arg(1), Arg(2), Arg(3)}, SmtlibType::memory(addr_width, data_width), {mem, addr, data});
	}

	T constant(RTLIL::Const value) { return node(SExpr(value), value.size(), {}); }
	T input(IdString name, int width) {
		module.input_struct.insert(name, width);
		return node(module.input_struct.access("inputs", name), width, {});
	}
	T state(IdString name, int width) {
		module.state_struct.insert(name, width);
		return node(module.state_struct.access("current_state", name), width, {});
	}
	T state_memory(IdString name, int addr_width, int data_width) {
		module.state_struct.insert(name, SmtlibType::memory(addr_width, data_width));
		return node(module.state_struct.access("current_state", name), SmtlibType::memory(addr_width, data_width), {});
	}
	T cell_output(T cell, IdString type, IdString name, int width) {
		if (is_single_output(type))
			return cell;
		else
			return node(SExpr {"cell_output", Arg(1), RTLIL::unescape_id(name)}, width, {cell});
	}
	T multiple(vector<T> args, int width) {
		vector<SExpr> expr;
		expr.reserve(args.size() + 1);
		expr.push_back("multiple");
		for(size_t i = 1; i <= args.size(); i++)
			expr.push_back(Arg(i));
		return graph.add(Node(SExpr(std::move(expr)), width), 0, args);
	}
	T undriven(int width) {
		return constant(RTLIL::Const(State::S0, width));
		//return node(SExpr {"undriven"}, width, {});
	}
	T create_pending(int width) {
		return node(SExpr(), width, {});
	}
	void update_pending(T pending, T node) {
		log_assert(pending.function().expr.is_none());
		pending.set_function(Node(Arg(1), pending.function().type));
		pending.append_arg(node);
	}
	void declare_output(T node, IdString name, int width) {
		module.output_struct.insert(name, width);
		node.assign_key(name);
	}
	void declare_state(T node, IdString name, int width) {
		module.state_struct.insert(name, width);
		node.assign_key(name);
	}
	void declare_state_memory(T node, IdString name, int addr_width, int data_width) {
		module.state_struct.insert(name, SmtlibType::memory(addr_width, data_width));
		node.assign_key(name);
	}
	void suggest_name(T node, IdString name) {
		node.sparse_attr() = name;
	}
};

void SmtlibModule::calculate_compute_graph(RTLIL::Module *module)
{
	SmtlibComputeGraphFactory factory(*this);
	ComputeGraphConstruction<SmtlibComputeGraph::Ref, SmtlibComputeGraphFactory> construction(factory);
	construction.add_module(module);
	construction.process_queue();

	// Perform topo sort and detect SCCs
	SmtlibComputeGraph::SccAdaptor compute_graph_scc(compute_graph);

	bool scc = false;
	std::vector<int> perm;
	topo_sorted_sccs(compute_graph_scc, [&](int *begin, int *end) {
		perm.insert(perm.end(), begin, end);
		if (end > begin + 1)
		{
			log_warning("SCC:");
			for (int *i = begin; i != end; ++i)
				log(" %d", *i);
			log("\n");
			scc = true;
		}
	}, /* sources_first */ true);
	compute_graph.permute(perm);
	if(scc) log_error("combinational loops, aborting\n");

	// Forward $$buf
	std::vector<int> alias;
	perm.clear();

	for (int i = 0; i < compute_graph.size(); ++i)
	{
		auto node = compute_graph[i];
		if (node.function().expr == Arg(1) && node.arg(0).index() < i)
		{
			int target_index = alias[node.arg(0).index()];
			auto target_node = compute_graph[perm[target_index]];
			if(!target_node.has_sparse_attr() && node.has_sparse_attr())
				target_node.sparse_attr() = node.sparse_attr();
			alias.push_back(target_index);
		}
		else
		{
			alias.push_back(GetSize(perm));
			perm.push_back(i);
		}
	}
	compute_graph.permute(perm, alias);
}

void SmtlibModule::write(std::ostream &stream)
{
	SmtlibWriter f(stream);

	idict<std::string> node_names;
	SmtlibScope locals;
	int paren_count = 0;

	input_struct.print(f);
	output_struct.print(f);
	state_struct.print(f);

	f << "(declare-datatypes ((Pair 2)) ((par (X Y) ((pair (first X) (second Y))))))\n";
	f.printf("(define-fun %s_step ((inputs %s_inputs) (current_state %s_state)) (Pair %s_outputs %s_state)\n",
		name.c_str(), name.c_str(), name.c_str(), name.c_str(), name.c_str());

	for (int i = 0; i < compute_graph.size(); ++i)
	{
		auto ref = compute_graph[i];
		std::string name;
		if(ref.has_sparse_attr())
			name = locals.insert(ref.sparse_attr());
		else
			name = locals.insert("\\n" + std::to_string(i));
		node_names(name);
		vector<SExpr> args;
		args.reserve(ref.size());
		for (int i = 0, end = ref.size(); i != end; ++i)
			args.push_back(node_names[ref.arg(i).index()]);
		f << "  (let " << SExpr{{SExpr{name, ref.function().expr.subst_args(args)}}} << "\n";
		paren_count++;
	}
	dict<IdString, SExpr> outputs;
	for(auto &a: compute_graph.keys())
		outputs.insert({a.first, node_names[a.second]});
	f.printf("    (pair \n");
	output_struct.print_value(f, outputs, 6);
	state_struct.print_value(f, outputs, 6);
	f.printf("    )\n");
	while(paren_count > 0){
		int n = min(paren_count, 80);
		f << "  " << std::string(n, ')') << "\n";
		paren_count -= n;
	}
	f.printf(")\n");
}

struct FunctionalSmtlibBackend : public Backend
{
	FunctionalSmtlibBackend() : Backend("functional_smtlib", "convert design to SMTLIB using the functional backend") {}

    void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
    }

	void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design) override
	{
        log_header(design, "Executing Functional SMTLIB backend.\n");

		size_t argidx = 1;
		extra_args(f, filename, args, argidx, design);

		for (auto module : design->selected_modules()) {
            log("Dumping module `%s'.\n", module->name.c_str());
			SmtlibModule smt(RTLIL::unescape_id(module->name));
			smt.calculate_compute_graph(module);
			smt.write(*f);
		}
	}
} FunctionalSmtlibBackend;

PRIVATE_NAMESPACE_END
