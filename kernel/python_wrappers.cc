/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
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

#ifdef WITH_PYTHON

#include "yosys.h"
#include <boost/python/module.hpp>
#include <boost/python/class.hpp>
#include <boost/python/wrapper.hpp>
#include <boost/python/call.hpp>
#include <boost/python.hpp>
#include <boost/log/exceptions.hpp>

using namespace Yosys;

namespace YOSYS_PYTHON {

	struct IdString;
	struct Const;
	struct CaseRule;
	struct SwitchRule;
	struct SyncRule;
	struct Process;
	struct SigChunk;
	struct SigBit;
	struct SigSpec;
	struct Cell;
	struct Wire;
	struct Memory;
	struct Module;
	struct Design;
	struct Monitor;
	typedef Yosys::RTLIL::State State;

	void run(std::string command)
	{
		Yosys::run_pass(command);
	}

	void log(std::string text)
	{
		Yosys::log("%s",text.c_str());
	}

	//WRAPPED from kernel/rtlil
	struct IdString
	{
		Yosys::RTLIL::IdString* ref_obj;

		IdString(Yosys::RTLIL::IdString* ref = new Yosys::RTLIL::IdString())
		{
			this->ref_obj = new Yosys::RTLIL::IdString(*ref);
		}

		~IdString()
		{
			delete(this->ref_obj);
		}

		IdString(Yosys::RTLIL::IdString ref)
		{
			this->ref_obj = new Yosys::RTLIL::IdString(ref);
		}

		IdString(const std::string &str)
		{
			this->ref_obj = new Yosys::RTLIL::IdString(str);
		}

		Yosys::RTLIL::IdString* get_cpp_obj() const
		{
			return ref_obj;
		}

		//WRAPPED static inline int get_reference(int idx)
		static int get_reference(int idx);

		//WRAPPED static inline void put_reference(int idx)
		static void put_reference(int idx);

		//WRAPPED std::string str() const {
		std::string str();

		//WRAPPED std::string substr(size_t pos = 0, size_t len = std::string::npos) const {
		std::string substr(size_t pos = 0, size_t len = std::string::npos);

		//WRAPPED size_t size() const {
		size_t size();

		//WRAPPED bool empty() const {
		bool empty();

		//WRAPPED void clear() {
		void clear();

		//WRAPPED unsigned int hash() const {
		unsigned int hash();

		//WRAPPED bool in(IdString rhs) const { return *this == rhs; }
		bool in_IdString(IdString *rhs);

		//WRAPPED bool in(const std::string &rhs) const { return *this == rhs; }
		bool in_std_string(std::string rhs);

		//WRAPPED bool in(const pool<IdString> &rhs) const { return rhs.count(*this) != 0; }
		bool in_pool_IdString(boost::python::list rhs);

		bool operator<(IdString rhs) { return get_cpp_obj() <rhs.get_cpp_obj(); }

		bool operator==(IdString rhs) { return get_cpp_obj() ==rhs.get_cpp_obj(); }

		bool operator!=(IdString rhs) { return get_cpp_obj() !=rhs.get_cpp_obj(); }
	};

	std::ostream &operator<<(std::ostream &ostr, const IdString &ref)
	{
		ostr << ref.ref_obj->str();
		return ostr;
	}
	//WRAPPED from kernel/rtlil
	struct Const
	{
		Yosys::RTLIL::Const* ref_obj;

		Const(Yosys::RTLIL::Const* ref = new Yosys::RTLIL::Const())
		{
			this->ref_obj = new Yosys::RTLIL::Const(*ref);
		}

		~Const()
		{
			delete(this->ref_obj);
		}

		Const(Yosys::RTLIL::Const ref)
		{
			this->ref_obj = new Yosys::RTLIL::Const(ref);
		}

		Yosys::RTLIL::Const* get_cpp_obj() const
		{
			return ref_obj;
		}

		//WRAPPED bool as_bool() const;
		bool as_bool();

		//WRAPPED int as_int(bool is_signed = false) const;
		int as_int(bool is_signed = false);

		//WRAPPED std::string as_string() const;
		std::string as_string();

		//WRAPPED static Const from_string(std::string str);
		static Const from_string(std::string str);

		//WRAPPED std::string decode_string() const;
		std::string decode_string();

		//WRAPPED inline int size() const { return bits.size(); }
		int size();

		//WRAPPED bool is_fully_zero() const;
		bool is_fully_zero();

		//WRAPPED bool is_fully_ones() const;
		bool is_fully_ones();

		//WRAPPED bool is_fully_def() const;
		bool is_fully_def();

		//WRAPPED bool is_fully_undef() const;
		bool is_fully_undef();

		//WRAPPED inline RTLIL::Const extract(int offset, int len = 1, RTLIL::State padding = RTLIL::State::S0) const {
		Const extract(int offset, int len = 1, State padding = RTLIL::State::S0);

		//WRAPPED inline unsigned int hash() const {
		unsigned int hash();

		bool operator<(Const rhs) { return get_cpp_obj() <rhs.get_cpp_obj(); }

		bool operator==(Const rhs) { return get_cpp_obj() ==rhs.get_cpp_obj(); }

		bool operator!=(Const rhs) { return get_cpp_obj() !=rhs.get_cpp_obj(); }
	};

	std::ostream &operator<<(std::ostream &ostr, const Const &ref)
	{
		ostr << ref.ref_obj->as_string();
		return ostr;
	}
	//WRAPPED from kernel/rtlil
	struct CaseRule
	{
		Yosys::RTLIL::CaseRule* ref_obj;

		CaseRule(Yosys::RTLIL::CaseRule* ref = new Yosys::RTLIL::CaseRule())
		{
			this->ref_obj = ref->clone();
		}

		~CaseRule()
		{
			delete(this->ref_obj);
		}

		CaseRule(Yosys::RTLIL::CaseRule ref)
		{
			this->ref_obj = ref.clone();
		}

		Yosys::RTLIL::CaseRule* get_cpp_obj() const
		{
			return ref_obj;
		}

		//WRAPPED RTLIL::CaseRule *clone() const;
		CaseRule clone();
	};

	std::ostream &operator<<(std::ostream &ostr, const CaseRule &ref)
	{
		ostr << "CaseRule object at " << ref.ref_obj;
		return ostr;
	}
	//WRAPPED from kernel/rtlil
	struct SwitchRule
	{
		Yosys::RTLIL::SwitchRule* ref_obj;

		SwitchRule(Yosys::RTLIL::SwitchRule* ref = new Yosys::RTLIL::SwitchRule())
		{
			this->ref_obj = ref->clone();
		}

		~SwitchRule()
		{
			delete(this->ref_obj);
		}

		SwitchRule(Yosys::RTLIL::SwitchRule ref)
		{
			this->ref_obj = ref.clone();
		}

		Yosys::RTLIL::SwitchRule* get_cpp_obj() const
		{
			return ref_obj;
		}

		//WRAPPED RTLIL::SwitchRule *clone() const;
		SwitchRule clone();
	};

	std::ostream &operator<<(std::ostream &ostr, const SwitchRule &ref)
	{
		ostr << "SwitchRule object at " << ref.ref_obj;
		return ostr;
	}
	//WRAPPED from kernel/rtlil
	struct SyncRule
	{
		Yosys::RTLIL::SyncRule* ref_obj;

		SyncRule(Yosys::RTLIL::SyncRule* ref = new Yosys::RTLIL::SyncRule())
		{
			this->ref_obj = ref->clone();
		}

		~SyncRule()
		{
			delete(this->ref_obj);
		}

		SyncRule(Yosys::RTLIL::SyncRule ref)
		{
			this->ref_obj = ref.clone();
		}

		Yosys::RTLIL::SyncRule* get_cpp_obj() const
		{
			return ref_obj;
		}

		//WRAPPED RTLIL::SyncRule *clone() const;
		SyncRule clone();
	};

	std::ostream &operator<<(std::ostream &ostr, const SyncRule &ref)
	{
		ostr << "SyncRule object at " << ref.ref_obj;
		return ostr;
	}
	//WRAPPED from kernel/rtlil
	struct Process
	{
		Yosys::RTLIL::Process* ref_obj;

		Process(Yosys::RTLIL::Process* ref = new Yosys::RTLIL::Process())
		{
			this->ref_obj = ref->clone();
		}

		~Process()
		{
			delete(this->ref_obj);
		}

		Process(Yosys::RTLIL::Process ref)
		{
			this->ref_obj = ref.clone();
		}

		Yosys::RTLIL::Process* get_cpp_obj() const
		{
			return ref_obj;
		}

		//WRAPPED RTLIL::Process *clone() const;
		Process clone();
	};

	std::ostream &operator<<(std::ostream &ostr, const Process &ref)
	{
		ostr << "Process with name " << ref.ref_obj->name.c_str();
		return ostr;
	}
	//WRAPPED from kernel/rtlil
	struct SigChunk
	{
		Yosys::RTLIL::SigChunk* ref_obj;

		SigChunk(Yosys::RTLIL::SigChunk* ref = new Yosys::RTLIL::SigChunk())
		{
			this->ref_obj = new Yosys::RTLIL::SigChunk(*ref);
		}

		~SigChunk()
		{
			delete(this->ref_obj);
		}

		SigChunk(Yosys::RTLIL::SigChunk ref)
		{
			this->ref_obj = new Yosys::RTLIL::SigChunk(ref);
		}

		Yosys::RTLIL::SigChunk* get_cpp_obj() const
		{
			return ref_obj;
		}

		//WRAPPED RTLIL::SigChunk extract(int offset, int length) const;
		SigChunk extract(int offset, int length);

		bool operator<(SigChunk rhs) { return get_cpp_obj() <rhs.get_cpp_obj(); }

		bool operator==(SigChunk rhs) { return get_cpp_obj() ==rhs.get_cpp_obj(); }

		bool operator!=(SigChunk rhs) { return get_cpp_obj() !=rhs.get_cpp_obj(); }
	};

	std::ostream &operator<<(std::ostream &ostr, const SigChunk &ref)
	{
		ostr << "SigChunk object at " << ref.ref_obj;
		return ostr;
	}
	//WRAPPED from kernel/rtlil
	struct SigBit
	{
		Yosys::RTLIL::SigBit* ref_obj;

		SigBit(Yosys::RTLIL::SigBit* ref = new Yosys::RTLIL::SigBit())
		{
			this->ref_obj = new Yosys::RTLIL::SigBit(*ref);
		}

		~SigBit()
		{
			delete(this->ref_obj);
		}

		SigBit(Yosys::RTLIL::SigBit ref)
		{
			this->ref_obj = new Yosys::RTLIL::SigBit(ref);
		}

		Yosys::RTLIL::SigBit* get_cpp_obj() const
		{
			return ref_obj;
		}

		//WRAPPED unsigned int hash() const;
		unsigned int hash();

		bool operator<(SigBit rhs) { return get_cpp_obj() <rhs.get_cpp_obj(); }

		bool operator==(SigBit rhs) { return get_cpp_obj() ==rhs.get_cpp_obj(); }

		bool operator!=(SigBit rhs) { return get_cpp_obj() !=rhs.get_cpp_obj(); }
	};

	std::ostream &operator<<(std::ostream &ostr, const SigBit &ref)
	{
		ostr << "SigBit object at " << ref.ref_obj;
		return ostr;
	}
	//WRAPPED from kernel/rtlil
	struct SigSpec
	{
		Yosys::RTLIL::SigSpec* ref_obj;

		SigSpec(Yosys::RTLIL::SigSpec* ref = new Yosys::RTLIL::SigSpec())
		{
			this->ref_obj = new Yosys::RTLIL::SigSpec(*ref);
		}

		~SigSpec()
		{
			delete(this->ref_obj);
		}

		SigSpec(Yosys::RTLIL::SigSpec ref)
		{
			this->ref_obj = new Yosys::RTLIL::SigSpec(ref);
		}

		Yosys::RTLIL::SigSpec* get_cpp_obj() const
		{
			return ref_obj;
		}

		//WRAPPED size_t get_hash() const {
		size_t get_hash();

		//WRAPPED inline int size() const { return width_; }
		int size();

		//WRAPPED inline bool empty() const { return width_ == 0; }
		bool empty();

		//WRAPPED void replace(const RTLIL::SigSpec &pattern, const RTLIL::SigSpec &with);
		void replace_SigSpec_SigSpec(SigSpec *pattern, SigSpec *with);

		//WRAPPED void replace(const RTLIL::SigSpec &pattern, const RTLIL::SigSpec &with, RTLIL::SigSpec *other) const;
		void replace_SigSpec_SigSpec_SigSpec(SigSpec *pattern, SigSpec *with, SigSpec *other);

		//WRAPPED void replace(int offset, const RTLIL::SigSpec &with);
		void replace_int_SigSpec(int offset, SigSpec *with);

		//WRAPPED void remove(const RTLIL::SigSpec &pattern);
		void remove_SigSpec(SigSpec *pattern);

		//WRAPPED void remove(const RTLIL::SigSpec &pattern, RTLIL::SigSpec *other) const;
		void remove_SigSpec_SigSpec(SigSpec *pattern, SigSpec *other);

		//WRAPPED void remove2(const RTLIL::SigSpec &pattern, RTLIL::SigSpec *other);
		void remove2_SigSpec_SigSpec(SigSpec *pattern, SigSpec *other);

		//WRAPPED void remove(const pool<RTLIL::SigBit> &pattern);
		void remove_pool_SigBit(boost::python::list pattern);

		//WRAPPED void remove(const pool<RTLIL::SigBit> &pattern, RTLIL::SigSpec *other) const;
		void remove_pool_SigBit_SigSpec(boost::python::list pattern, SigSpec *other);

		//WRAPPED void remove2(const pool<RTLIL::SigBit> &pattern, RTLIL::SigSpec *other);
		void remove2_pool_SigBit_SigSpec(boost::python::list pattern, SigSpec *other);

		//WRAPPED void remove(int offset, int length = 1);
		void remove_int_int(int offset, int length = 1);

		//WRAPPED RTLIL::SigSpec extract(const RTLIL::SigSpec &pattern, const RTLIL::SigSpec *other = NULL) const;
		SigSpec extract_SigSpec_SigSpec(SigSpec *pattern, SigSpec *other);

		//WRAPPED RTLIL::SigSpec extract(const pool<RTLIL::SigBit> &pattern, const RTLIL::SigSpec *other = NULL) const;
		SigSpec extract_pool_SigBit_SigSpec(boost::python::list pattern, SigSpec *other);

		//WRAPPED RTLIL::SigSpec extract(int offset, int length = 1) const;
		SigSpec extract_int_int(int offset, int length = 1);

		//WRAPPED void append(const RTLIL::SigSpec &signal);
		void append(SigSpec *signal);

		//WRAPPED void append_bit(const RTLIL::SigBit &bit);
		void append_bit(SigBit *bit);

		//WRAPPED void extend_u0(int width, bool is_signed = false);
		void extend_u0(int width, bool is_signed = false);

		//WRAPPED RTLIL::SigSpec repeat(int num) const;
		SigSpec repeat(int num);

		//WRAPPED bool is_wire() const;
		bool is_wire();

		//WRAPPED bool is_chunk() const;
		bool is_chunk();

		//WRAPPED inline bool is_bit() const { return width_ == 1; }
		bool is_bit();

		//WRAPPED bool is_fully_const() const;
		bool is_fully_const();

		//WRAPPED bool is_fully_zero() const;
		bool is_fully_zero();

		//WRAPPED bool is_fully_ones() const;
		bool is_fully_ones();

		//WRAPPED bool is_fully_def() const;
		bool is_fully_def();

		//WRAPPED bool is_fully_undef() const;
		bool is_fully_undef();

		//WRAPPED bool has_const() const;
		bool has_const();

		//WRAPPED bool has_marked_bits() const;
		bool has_marked_bits();

		//WRAPPED bool as_bool() const;
		bool as_bool();

		//WRAPPED int as_int(bool is_signed = false) const;
		int as_int(bool is_signed = false);

		//WRAPPED std::string as_string() const;
		std::string as_string();

		//WRAPPED RTLIL::Const as_const() const;
		Const as_const();

		//WRAPPED RTLIL::Wire *as_wire() const;
		Wire as_wire();

		//WRAPPED RTLIL::SigChunk as_chunk() const;
		SigChunk as_chunk();

		//WRAPPED RTLIL::SigBit as_bit() const;
		SigBit as_bit();

		//WRAPPED bool match(std::string pattern) const;
		bool match(std::string pattern);

		//WRAPPED static bool parse(RTLIL::SigSpec &sig, RTLIL::Module *module, std::string str);
		static bool parse(SigSpec *sig, Module *module, std::string str);

		//WRAPPED static bool parse_sel(RTLIL::SigSpec &sig, RTLIL::Design *design, RTLIL::Module *module, std::string str);
		static bool parse_sel(SigSpec *sig, Design *design, Module *module, std::string str);

		//WRAPPED static bool parse_rhs(const RTLIL::SigSpec &lhs, RTLIL::SigSpec &sig, RTLIL::Module *module, std::string str);
		static bool parse_rhs(SigSpec *lhs, SigSpec *sig, Module *module, std::string str);

		//WRAPPED unsigned int hash() const { if(!hash_) updhash(); return hash_; };
		unsigned int hash();

		//WRAPPED void check() const;
		void check();

		bool operator<(SigSpec rhs) { return get_cpp_obj() <rhs.get_cpp_obj(); }

		bool operator==(SigSpec rhs) { return get_cpp_obj() ==rhs.get_cpp_obj(); }

		bool operator!=(SigSpec rhs) { return get_cpp_obj() !=rhs.get_cpp_obj(); }
	};

	std::ostream &operator<<(std::ostream &ostr, const SigSpec &ref)
	{
		ostr << "SigSpec object at " << ref.ref_obj;
		return ostr;
	}
	//WRAPPED from kernel/rtlil
	struct Cell
	{
		unsigned int hashidx_;
		Yosys::RTLIL::Cell* ref_obj;

		Cell(Yosys::RTLIL::Cell* ref)
		{
			this->hashidx_ = ref->hashidx_;
			this->ref_obj = ref;
		}

		Yosys::RTLIL::Cell* get_cpp_obj() const
		{
			Yosys::RTLIL::Cell* ret = Yosys::RTLIL::Cell::get_all_cells()->at(this->hashidx_);
			if(ret != NULL && ret == this->ref_obj)
				return ret;
			return NULL;
		}

		//WRAPPED unsigned int hash() const { return hashidx_; }
		unsigned int hash();

		//WRAPPED bool hasPort(RTLIL::IdString portname) const;
		bool hasPort(IdString *portname);

		//WRAPPED void unsetPort(RTLIL::IdString portname);
		void unsetPort(IdString *portname);

		//WRAPPED void setPort(RTLIL::IdString portname, RTLIL::SigSpec signal);
		void setPort(IdString *portname, SigSpec *signal);

		//WRAPPED bool known() const;
		bool known();

		//WRAPPED bool input(RTLIL::IdString portname) const;
		bool input(IdString *portname);

		//WRAPPED bool output(RTLIL::IdString portname) const;
		bool output(IdString *portname);

		//WRAPPED bool hasParam(RTLIL::IdString paramname) const;
		bool hasParam(IdString *paramname);

		//WRAPPED void unsetParam(RTLIL::IdString paramname);
		void unsetParam(IdString *paramname);

		//WRAPPED void setParam(RTLIL::IdString paramname, RTLIL::Const value);
		void setParam(IdString *paramname, Const *value);

		//WRAPPED void fixup_parameters(bool set_a_signed = false, bool set_b_signed = false);
		void fixup_parameters(bool set_a_signed = false, bool set_b_signed = false);

		//WRAPPED bool has_keep_attr() const {
		bool has_keep_attr();
	};

	std::ostream &operator<<(std::ostream &ostr, const Cell &ref)
	{
		if(ref.get_cpp_obj() != NULL)
			ostr << "Cell with name " << ref.get_cpp_obj()->name.c_str();
		else
			ostr << "deleted Cell";
		return ostr;
	}
	//WRAPPED from kernel/rtlil
	struct Wire
	{
		unsigned int hashidx_;
		Yosys::RTLIL::Wire* ref_obj;

		Wire(Yosys::RTLIL::Wire* ref)
		{
			this->hashidx_ = ref->hashidx_;
			this->ref_obj = ref;
		}

		Yosys::RTLIL::Wire* get_cpp_obj() const
		{
			Yosys::RTLIL::Wire* ret = Yosys::RTLIL::Wire::get_all_wires()->at(this->hashidx_);
			if(ret != NULL && ret == this->ref_obj)
				return ret;
			return NULL;
		}

		//WRAPPED unsigned int hash() const { return hashidx_; }
		unsigned int hash();
	};

	std::ostream &operator<<(std::ostream &ostr, const Wire &ref)
	{
		if(ref.get_cpp_obj() != NULL)
			ostr << "Wire with name " << ref.get_cpp_obj()->name.c_str();
		else
			ostr << "deleted Wire";
		return ostr;
	}
	//WRAPPED from kernel/rtlil
	struct Memory
	{
		unsigned int hashidx_;
		Yosys::RTLIL::Memory* ref_obj;

		Memory(Yosys::RTLIL::Memory* ref)
		{
			this->hashidx_ = ref->hashidx_;
			this->ref_obj = ref;
		}

		Yosys::RTLIL::Memory* get_cpp_obj() const
		{
			Yosys::RTLIL::Memory* ret = Yosys::RTLIL::Memory::get_all_memorys()->at(this->hashidx_);
			if(ret != NULL && ret == this->ref_obj)
				return ret;
			return NULL;
		}

		//WRAPPED unsigned int hash() const { return hashidx_; }
		unsigned int hash();
	};

	std::ostream &operator<<(std::ostream &ostr, const Memory &ref)
	{
		if(ref.get_cpp_obj() != NULL)
			ostr << "Memory with name " << ref.get_cpp_obj()->name.c_str();
		else
			ostr << "deleted Memory";
		return ostr;
	}
	//WRAPPED from kernel/rtlil
	struct Module
	{
		unsigned int hashidx_;
		Yosys::RTLIL::Module* ref_obj;

		Module(Yosys::RTLIL::Module* ref = new Yosys::RTLIL::Module())
		{
			this->hashidx_ = ref->hashidx_;
			this->ref_obj = ref;
		}

		Yosys::RTLIL::Module* get_cpp_obj() const
		{
			Yosys::RTLIL::Module* ret = Yosys::RTLIL::Module::get_all_modules()->at(this->hashidx_);
			if(ret != NULL && ret == this->ref_obj)
				return ret;
			return NULL;
		}

		boost::python::list get_cells()
		{
			Yosys::RTLIL::Module* cpp_obj = get_cpp_obj();
			boost::python::list result;
			if(cpp_obj == NULL)
			{
				return result;
			}
			for(auto &mod_it : cpp_obj->cells_)
			{
				result.append(Cell(mod_it.second));
			}
			return result;
		}

		boost::python::list get_wires()
		{
			Yosys::RTLIL::Module* cpp_obj = get_cpp_obj();
			boost::python::list result;
			if(cpp_obj == NULL)
			{
				return result;
			}
			for(auto &mod_it : cpp_obj->wires_)
			{
				result.append(Wire(mod_it.second));
			}
			return result;
		}

		void register_monitor(Monitor* const m);

		//WRAPPED unsigned int hash() const { return hashidx_; }
		unsigned int hash();

		//WRAPPED void connect(const RTLIL::SigSig &conn);
		void connect_SigSig(PyObject *conn);

		//WRAPPED void connect(const RTLIL::SigSpec &lhs, const RTLIL::SigSpec &rhs);
		void connect_SigSpec_SigSpec(SigSpec *lhs, SigSpec *rhs);

		//WRAPPED void new_connections(const std::vector<RTLIL::SigSig> &new_conn);
		void new_connections(boost::python::list new_conn);

		//WRAPPED void cloneInto(RTLIL::Module *new_mod) const;
		void cloneInto(Module *new_mod);

		//WRAPPED bool has_memories() const;
		bool has_memories();

		//WRAPPED bool has_processes() const;
		bool has_processes();

		//WRAPPED bool has_memories_warn() const;
		bool has_memories_warn();

		//WRAPPED bool has_processes_warn() const;
		bool has_processes_warn();

		//WRAPPED RTLIL::Wire* wire(RTLIL::IdString id) { return wires_.count(id) ? wires_.at(id) : nullptr; }
		Wire wire(IdString *id);

		//WRAPPED RTLIL::Cell* cell(RTLIL::IdString id) { return cells_.count(id) ? cells_.at(id) : nullptr; }
		Cell cell(IdString *id);

		//WRAPPED void remove(const pool<RTLIL::Wire*> &wires);
		void remove_pool_Wire(boost::python::list wires);

		//WRAPPED void remove(RTLIL::Cell *cell);
		void remove_Cell(Cell *cell);

		//WRAPPED void rename(RTLIL::Wire *wire, RTLIL::IdString new_name);
		void rename_Wire_IdString(Wire *wire, IdString *new_name);

		//WRAPPED void rename(RTLIL::Cell *cell, RTLIL::IdString new_name);
		void rename_Cell_IdString(Cell *cell, IdString *new_name);

		//WRAPPED void rename(RTLIL::IdString old_name, RTLIL::IdString new_name);
		void rename_IdString_IdString(IdString *old_name, IdString *new_name);

		//WRAPPED void swap_names(RTLIL::Wire *w1, RTLIL::Wire *w2);
		void swap_names_Wire_Wire(Wire *w1, Wire *w2);

		//WRAPPED void swap_names(RTLIL::Cell *c1, RTLIL::Cell *c2);
		void swap_names_Cell_Cell(Cell *c1, Cell *c2);

		//WRAPPED RTLIL::IdString uniquify(RTLIL::IdString name);
		IdString uniquify_IdString(IdString *name);

		//WRAPPED RTLIL::IdString uniquify(RTLIL::IdString name, int &index);
		IdString uniquify_IdString_int(IdString *name, int index);

		//WRAPPED RTLIL::Wire *addWire(RTLIL::IdString name, int width = 1);
		Wire addWire_IdString_int(IdString *name, int width = 1);

		//WRAPPED RTLIL::Wire *addWire(RTLIL::IdString name, const RTLIL::Wire *other);
		Wire addWire_IdString_Wire(IdString *name, Wire *other);

		//WRAPPED RTLIL::Cell *addCell(RTLIL::IdString name, RTLIL::IdString type);
		Cell addCell_IdString_IdString(IdString *name, IdString *type);

		//WRAPPED RTLIL::Cell *addCell(RTLIL::IdString name, const RTLIL::Cell *other);
		Cell addCell_IdString_Cell(IdString *name, Cell *other);

		//WRAPPED RTLIL::Cell* addNot(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = "");
		Cell addNot(IdString *name, SigSpec *sig_a, SigSpec *sig_y, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::Cell* addPos(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = "");
		Cell addPos(IdString *name, SigSpec *sig_a, SigSpec *sig_y, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::Cell* addNeg(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = "");
		Cell addNeg(IdString *name, SigSpec *sig_a, SigSpec *sig_y, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::Cell* addAnd(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = "");
		Cell addAnd(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::Cell* addOr(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = "");
		Cell addOr(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::Cell* addXor(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = "");
		Cell addXor(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::Cell* addXnor(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = "");
		Cell addXnor(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::Cell* addReduceAnd(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = "");
		Cell addReduceAnd(IdString *name, SigSpec *sig_a, SigSpec *sig_y, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::Cell* addReduceOr(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = "");
		Cell addReduceOr(IdString *name, SigSpec *sig_a, SigSpec *sig_y, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::Cell* addReduceXor(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = "");
		Cell addReduceXor(IdString *name, SigSpec *sig_a, SigSpec *sig_y, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::Cell* addReduceXnor(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = "");
		Cell addReduceXnor(IdString *name, SigSpec *sig_a, SigSpec *sig_y, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::Cell* addReduceBool(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = "");
		Cell addReduceBool(IdString *name, SigSpec *sig_a, SigSpec *sig_y, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::Cell* addShl(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = "");
		Cell addShl(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::Cell* addShr(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = "");
		Cell addShr(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::Cell* addSshl(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = "");
		Cell addSshl(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::Cell* addSshr(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = "");
		Cell addSshr(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::Cell* addShift(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = "");
		Cell addShift(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::Cell* addShiftx(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = "");
		Cell addShiftx(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::Cell* addLt(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = "");
		Cell addLt(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::Cell* addLe(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = "");
		Cell addLe(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::Cell* addEq(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = "");
		Cell addEq(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::Cell* addNe(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = "");
		Cell addNe(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::Cell* addEqx(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = "");
		Cell addEqx(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::Cell* addNex(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = "");
		Cell addNex(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::Cell* addGe(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = "");
		Cell addGe(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::Cell* addGt(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = "");
		Cell addGt(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::Cell* addAdd(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = "");
		Cell addAdd(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::Cell* addSub(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = "");
		Cell addSub(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::Cell* addMul(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = "");
		Cell addMul(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::Cell* addDiv(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = "");
		Cell addDiv(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::Cell* addMod(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = "");
		Cell addMod(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::Cell* addPow(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool a_signed = false, bool b_signed = false, const std::string &src = "");
		Cell addPow(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool a_signed = false, bool b_signed = false, std::string src = "");

		//WRAPPED RTLIL::Cell* addLogicNot(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = "");
		Cell addLogicNot(IdString *name, SigSpec *sig_a, SigSpec *sig_y, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::Cell* addLogicAnd(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = "");
		Cell addLogicAnd(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::Cell* addLogicOr(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = "");
		Cell addLogicOr(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::Cell* addMux(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_s, RTLIL::SigSpec sig_y, const std::string &src = "");
		Cell addMux(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_s, SigSpec *sig_y, std::string src = "");

		//WRAPPED RTLIL::Cell* addPmux(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_s, RTLIL::SigSpec sig_y, const std::string &src = "");
		Cell addPmux(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_s, SigSpec *sig_y, std::string src = "");

		//WRAPPED RTLIL::Cell* addSlice(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_y, RTLIL::Const offset, const std::string &src = "");
		Cell addSlice(IdString *name, SigSpec *sig_a, SigSpec *sig_y, Const *offset, std::string src = "");

		//WRAPPED RTLIL::Cell* addConcat(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, const std::string &src = "");
		Cell addConcat(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, std::string src = "");

		//WRAPPED RTLIL::Cell* addLut(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_y, RTLIL::Const lut, const std::string &src = "");
		Cell addLut(IdString *name, SigSpec *sig_a, SigSpec *sig_y, Const *lut, std::string src = "");

		//WRAPPED RTLIL::Cell* addTribuf(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_en, RTLIL::SigSpec sig_y, const std::string &src = "");
		Cell addTribuf(IdString *name, SigSpec *sig_a, SigSpec *sig_en, SigSpec *sig_y, std::string src = "");

		//WRAPPED RTLIL::Cell* addAssert(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_en, const std::string &src = "");
		Cell addAssert(IdString *name, SigSpec *sig_a, SigSpec *sig_en, std::string src = "");

		//WRAPPED RTLIL::Cell* addAssume(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_en, const std::string &src = "");
		Cell addAssume(IdString *name, SigSpec *sig_a, SigSpec *sig_en, std::string src = "");

		//WRAPPED RTLIL::Cell* addLive(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_en, const std::string &src = "");
		Cell addLive(IdString *name, SigSpec *sig_a, SigSpec *sig_en, std::string src = "");

		//WRAPPED RTLIL::Cell* addFair(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_en, const std::string &src = "");
		Cell addFair(IdString *name, SigSpec *sig_a, SigSpec *sig_en, std::string src = "");

		//WRAPPED RTLIL::Cell* addCover(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_en, const std::string &src = "");
		Cell addCover(IdString *name, SigSpec *sig_a, SigSpec *sig_en, std::string src = "");

		//WRAPPED RTLIL::Cell* addEquiv(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, const std::string &src = "");
		Cell addEquiv(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, std::string src = "");

		//WRAPPED RTLIL::Cell* addSr(RTLIL::IdString name, RTLIL::SigSpec sig_set, RTLIL::SigSpec sig_clr, RTLIL::SigSpec sig_q, bool set_polarity = true, bool clr_polarity = true, const std::string &src = "");
		Cell addSr(IdString *name, SigSpec *sig_set, SigSpec *sig_clr, SigSpec *sig_q, bool set_polarity = true, bool clr_polarity = true, std::string src = "");

		//WRAPPED RTLIL::Cell* addFf(RTLIL::IdString name, RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, const std::string &src = "");
		Cell addFf(IdString *name, SigSpec *sig_d, SigSpec *sig_q, std::string src = "");

		//WRAPPED RTLIL::Cell* addDff(RTLIL::IdString name, RTLIL::SigSpec sig_clk, RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool clk_polarity = true, const std::string &src = "");
		Cell addDff(IdString *name, SigSpec *sig_clk, SigSpec *sig_d, SigSpec *sig_q, bool clk_polarity = true, std::string src = "");

		//WRAPPED RTLIL::Cell* addDffe(RTLIL::IdString name, RTLIL::SigSpec sig_clk, RTLIL::SigSpec sig_en, RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool clk_polarity = true, bool en_polarity = true, const std::string &src = "");
		Cell addDffe(IdString *name, SigSpec *sig_clk, SigSpec *sig_en, SigSpec *sig_d, SigSpec *sig_q, bool clk_polarity = true, bool en_polarity = true, std::string src = "");

		//WRAPPED RTLIL::Cell* addDffsr(RTLIL::IdString name, RTLIL::SigSpec sig_clk, RTLIL::SigSpec sig_set, RTLIL::SigSpec sig_clr,RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool clk_polarity = true, bool set_polarity = true, bool clr_polarity = true, const std::string &src = "");
		Cell addDffsr(IdString *name, SigSpec *sig_clk, SigSpec *sig_set, SigSpec *sig_clr, SigSpec *sig_d, SigSpec *sig_q, bool clk_polarity = true, bool set_polarity = true, bool clr_polarity = true, std::string src = "");

		//WRAPPED RTLIL::Cell* addAdff(RTLIL::IdString name, RTLIL::SigSpec sig_clk, RTLIL::SigSpec sig_arst, RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q,RTLIL::Const arst_value, bool clk_polarity = true, bool arst_polarity = true, const std::string &src = "");
		Cell addAdff(IdString *name, SigSpec *sig_clk, SigSpec *sig_arst, SigSpec *sig_d, SigSpec *sig_q, Const *arst_value, bool clk_polarity = true, bool arst_polarity = true, std::string src = "");

		//WRAPPED RTLIL::Cell* addDlatch(RTLIL::IdString name, RTLIL::SigSpec sig_en, RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool en_polarity = true, const std::string &src = "");
		Cell addDlatch(IdString *name, SigSpec *sig_en, SigSpec *sig_d, SigSpec *sig_q, bool en_polarity = true, std::string src = "");

		//WRAPPED RTLIL::Cell* addDlatchsr(RTLIL::IdString name, RTLIL::SigSpec sig_en, RTLIL::SigSpec sig_set, RTLIL::SigSpec sig_clr,RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool en_polarity = true, bool set_polarity = true, bool clr_polarity = true, const std::string &src = "");
		Cell addDlatchsr(IdString *name, SigSpec *sig_en, SigSpec *sig_set, SigSpec *sig_clr, SigSpec *sig_d, SigSpec *sig_q, bool en_polarity = true, bool set_polarity = true, bool clr_polarity = true, std::string src = "");

		//WRAPPED RTLIL::Cell* addBufGate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_y, const std::string &src = "");
		Cell addBufGate(IdString *name, SigBit *sig_a, SigBit *sig_y, std::string src = "");

		//WRAPPED RTLIL::Cell* addNotGate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_y, const std::string &src = "");
		Cell addNotGate(IdString *name, SigBit *sig_a, SigBit *sig_y, std::string src = "");

		//WRAPPED RTLIL::Cell* addAndGate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, RTLIL::SigBit sig_y, const std::string &src = "");
		Cell addAndGate(IdString *name, SigBit *sig_a, SigBit *sig_b, SigBit *sig_y, std::string src = "");

		//WRAPPED RTLIL::Cell* addNandGate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, RTLIL::SigBit sig_y, const std::string &src = "");
		Cell addNandGate(IdString *name, SigBit *sig_a, SigBit *sig_b, SigBit *sig_y, std::string src = "");

		//WRAPPED RTLIL::Cell* addOrGate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, RTLIL::SigBit sig_y, const std::string &src = "");
		Cell addOrGate(IdString *name, SigBit *sig_a, SigBit *sig_b, SigBit *sig_y, std::string src = "");

		//WRAPPED RTLIL::Cell* addNorGate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, RTLIL::SigBit sig_y, const std::string &src = "");
		Cell addNorGate(IdString *name, SigBit *sig_a, SigBit *sig_b, SigBit *sig_y, std::string src = "");

		//WRAPPED RTLIL::Cell* addXorGate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, RTLIL::SigBit sig_y, const std::string &src = "");
		Cell addXorGate(IdString *name, SigBit *sig_a, SigBit *sig_b, SigBit *sig_y, std::string src = "");

		//WRAPPED RTLIL::Cell* addXnorGate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, RTLIL::SigBit sig_y, const std::string &src = "");
		Cell addXnorGate(IdString *name, SigBit *sig_a, SigBit *sig_b, SigBit *sig_y, std::string src = "");

		//WRAPPED RTLIL::Cell* addAndnotGate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, RTLIL::SigBit sig_y, const std::string &src = "");
		Cell addAndnotGate(IdString *name, SigBit *sig_a, SigBit *sig_b, SigBit *sig_y, std::string src = "");

		//WRAPPED RTLIL::Cell* addOrnotGate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, RTLIL::SigBit sig_y, const std::string &src = "");
		Cell addOrnotGate(IdString *name, SigBit *sig_a, SigBit *sig_b, SigBit *sig_y, std::string src = "");

		//WRAPPED RTLIL::Cell* addMuxGate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, RTLIL::SigBit sig_s, RTLIL::SigBit sig_y, const std::string &src = "");
		Cell addMuxGate(IdString *name, SigBit *sig_a, SigBit *sig_b, SigBit *sig_s, SigBit *sig_y, std::string src = "");

		//WRAPPED RTLIL::Cell* addAoi3Gate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, RTLIL::SigBit sig_c, RTLIL::SigBit sig_y, const std::string &src = "");
		Cell addAoi3Gate(IdString *name, SigBit *sig_a, SigBit *sig_b, SigBit *sig_c, SigBit *sig_y, std::string src = "");

		//WRAPPED RTLIL::Cell* addOai3Gate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, RTLIL::SigBit sig_c, RTLIL::SigBit sig_y, const std::string &src = "");
		Cell addOai3Gate(IdString *name, SigBit *sig_a, SigBit *sig_b, SigBit *sig_c, SigBit *sig_y, std::string src = "");

		//WRAPPED RTLIL::Cell* addAoi4Gate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, RTLIL::SigBit sig_c, RTLIL::SigBit sig_d, RTLIL::SigBit sig_y, const std::string &src = "");
		Cell addAoi4Gate(IdString *name, SigBit *sig_a, SigBit *sig_b, SigBit *sig_c, SigBit *sig_d, SigBit *sig_y, std::string src = "");

		//WRAPPED RTLIL::Cell* addOai4Gate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, RTLIL::SigBit sig_c, RTLIL::SigBit sig_d, RTLIL::SigBit sig_y, const std::string &src = "");
		Cell addOai4Gate(IdString *name, SigBit *sig_a, SigBit *sig_b, SigBit *sig_c, SigBit *sig_d, SigBit *sig_y, std::string src = "");

		//WRAPPED RTLIL::Cell* addFfGate(RTLIL::IdString name, RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, const std::string &src = "");
		Cell addFfGate(IdString *name, SigSpec *sig_d, SigSpec *sig_q, std::string src = "");

		//WRAPPED RTLIL::Cell* addDffGate(RTLIL::IdString name, RTLIL::SigSpec sig_clk, RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool clk_polarity = true, const std::string &src = "");
		Cell addDffGate(IdString *name, SigSpec *sig_clk, SigSpec *sig_d, SigSpec *sig_q, bool clk_polarity = true, std::string src = "");

		//WRAPPED RTLIL::Cell* addDffeGate(RTLIL::IdString name, RTLIL::SigSpec sig_clk, RTLIL::SigSpec sig_en, RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool clk_polarity = true, bool en_polarity = true, const std::string &src = "");
		Cell addDffeGate(IdString *name, SigSpec *sig_clk, SigSpec *sig_en, SigSpec *sig_d, SigSpec *sig_q, bool clk_polarity = true, bool en_polarity = true, std::string src = "");

		//WRAPPED RTLIL::Cell* addDffsrGate(RTLIL::IdString name, RTLIL::SigSpec sig_clk, RTLIL::SigSpec sig_set, RTLIL::SigSpec sig_clr,RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool clk_polarity = true, bool set_polarity = true, bool clr_polarity = true, const std::string &src = "");
		Cell addDffsrGate(IdString *name, SigSpec *sig_clk, SigSpec *sig_set, SigSpec *sig_clr, SigSpec *sig_d, SigSpec *sig_q, bool clk_polarity = true, bool set_polarity = true, bool clr_polarity = true, std::string src = "");

		//WRAPPED RTLIL::Cell* addAdffGate(RTLIL::IdString name, RTLIL::SigSpec sig_clk, RTLIL::SigSpec sig_arst, RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q,bool arst_value = false, bool clk_polarity = true, bool arst_polarity = true, const std::string &src = "");
		Cell addAdffGate(IdString *name, SigSpec *sig_clk, SigSpec *sig_arst, SigSpec *sig_d, SigSpec *sig_q, bool arst_value = false, bool clk_polarity = true, bool arst_polarity = true, std::string src = "");

		//WRAPPED RTLIL::Cell* addDlatchGate(RTLIL::IdString name, RTLIL::SigSpec sig_en, RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool en_polarity = true, const std::string &src = "");
		Cell addDlatchGate(IdString *name, SigSpec *sig_en, SigSpec *sig_d, SigSpec *sig_q, bool en_polarity = true, std::string src = "");

		//WRAPPED RTLIL::Cell* addDlatchsrGate(RTLIL::IdString name, RTLIL::SigSpec sig_en, RTLIL::SigSpec sig_set, RTLIL::SigSpec sig_clr,RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool en_polarity = true, bool set_polarity = true, bool clr_polarity = true, const std::string &src = "");
		Cell addDlatchsrGate(IdString *name, SigSpec *sig_en, SigSpec *sig_set, SigSpec *sig_clr, SigSpec *sig_d, SigSpec *sig_q, bool en_polarity = true, bool set_polarity = true, bool clr_polarity = true, std::string src = "");

		//WRAPPED RTLIL::SigSpec Not(RTLIL::IdString name, RTLIL::SigSpec sig_a, bool is_signed = false, const std::string &src = "");
		SigSpec Not(IdString *name, SigSpec *sig_a, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::SigSpec Pos(RTLIL::IdString name, RTLIL::SigSpec sig_a, bool is_signed = false, const std::string &src = "");
		SigSpec Pos(IdString *name, SigSpec *sig_a, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::SigSpec Neg(RTLIL::IdString name, RTLIL::SigSpec sig_a, bool is_signed = false, const std::string &src = "");
		SigSpec Neg(IdString *name, SigSpec *sig_a, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::SigSpec And(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = "");
		SigSpec And(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::SigSpec Or(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = "");
		SigSpec Or(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::SigSpec Xor(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = "");
		SigSpec Xor(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::SigSpec Xnor(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = "");
		SigSpec Xnor(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::SigSpec ReduceAnd(RTLIL::IdString name, RTLIL::SigSpec sig_a, bool is_signed = false, const std::string &src = "");
		SigSpec ReduceAnd(IdString *name, SigSpec *sig_a, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::SigSpec ReduceOr(RTLIL::IdString name, RTLIL::SigSpec sig_a, bool is_signed = false, const std::string &src = "");
		SigSpec ReduceOr(IdString *name, SigSpec *sig_a, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::SigSpec ReduceXor(RTLIL::IdString name, RTLIL::SigSpec sig_a, bool is_signed = false, const std::string &src = "");
		SigSpec ReduceXor(IdString *name, SigSpec *sig_a, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::SigSpec ReduceXnor(RTLIL::IdString name, RTLIL::SigSpec sig_a, bool is_signed = false, const std::string &src = "");
		SigSpec ReduceXnor(IdString *name, SigSpec *sig_a, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::SigSpec ReduceBool(RTLIL::IdString name, RTLIL::SigSpec sig_a, bool is_signed = false, const std::string &src = "");
		SigSpec ReduceBool(IdString *name, SigSpec *sig_a, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::SigSpec Shl(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = "");
		SigSpec Shl(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::SigSpec Shr(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = "");
		SigSpec Shr(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::SigSpec Sshl(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = "");
		SigSpec Sshl(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::SigSpec Sshr(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = "");
		SigSpec Sshr(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::SigSpec Shift(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = "");
		SigSpec Shift(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::SigSpec Shiftx(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = "");
		SigSpec Shiftx(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::SigSpec Lt(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = "");
		SigSpec Lt(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::SigSpec Le(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = "");
		SigSpec Le(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::SigSpec Eq(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = "");
		SigSpec Eq(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::SigSpec Ne(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = "");
		SigSpec Ne(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::SigSpec Eqx(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = "");
		SigSpec Eqx(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::SigSpec Nex(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = "");
		SigSpec Nex(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::SigSpec Ge(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = "");
		SigSpec Ge(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::SigSpec Gt(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = "");
		SigSpec Gt(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::SigSpec Add(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = "");
		SigSpec Add(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::SigSpec Sub(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = "");
		SigSpec Sub(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::SigSpec Mul(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = "");
		SigSpec Mul(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::SigSpec Div(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = "");
		SigSpec Div(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::SigSpec Mod(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = "");
		SigSpec Mod(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::SigSpec LogicNot(RTLIL::IdString name, RTLIL::SigSpec sig_a, bool is_signed = false, const std::string &src = "");
		SigSpec LogicNot(IdString *name, SigSpec *sig_a, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::SigSpec LogicAnd(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = "");
		SigSpec LogicAnd(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::SigSpec LogicOr(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = "");
		SigSpec LogicOr(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed = false, std::string src = "");

		//WRAPPED RTLIL::SigSpec Mux(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_s, const std::string &src = "");
		SigSpec Mux(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_s, std::string src = "");

		//WRAPPED RTLIL::SigSpec Pmux(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_s, const std::string &src = "");
		SigSpec Pmux(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_s, std::string src = "");

		//WRAPPED RTLIL::SigBit BufGate(RTLIL::IdString name, RTLIL::SigBit sig_a, const std::string &src = "");
		SigBit BufGate(IdString *name, SigBit *sig_a, std::string src = "");

		//WRAPPED RTLIL::SigBit NotGate(RTLIL::IdString name, RTLIL::SigBit sig_a, const std::string &src = "");
		SigBit NotGate(IdString *name, SigBit *sig_a, std::string src = "");

		//WRAPPED RTLIL::SigBit AndGate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, const std::string &src = "");
		SigBit AndGate(IdString *name, SigBit *sig_a, SigBit *sig_b, std::string src = "");

		//WRAPPED RTLIL::SigBit NandGate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, const std::string &src = "");
		SigBit NandGate(IdString *name, SigBit *sig_a, SigBit *sig_b, std::string src = "");

		//WRAPPED RTLIL::SigBit OrGate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, const std::string &src = "");
		SigBit OrGate(IdString *name, SigBit *sig_a, SigBit *sig_b, std::string src = "");

		//WRAPPED RTLIL::SigBit NorGate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, const std::string &src = "");
		SigBit NorGate(IdString *name, SigBit *sig_a, SigBit *sig_b, std::string src = "");

		//WRAPPED RTLIL::SigBit XorGate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, const std::string &src = "");
		SigBit XorGate(IdString *name, SigBit *sig_a, SigBit *sig_b, std::string src = "");

		//WRAPPED RTLIL::SigBit XnorGate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, const std::string &src = "");
		SigBit XnorGate(IdString *name, SigBit *sig_a, SigBit *sig_b, std::string src = "");

		//WRAPPED RTLIL::SigBit AndnotGate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, const std::string &src = "");
		SigBit AndnotGate(IdString *name, SigBit *sig_a, SigBit *sig_b, std::string src = "");

		//WRAPPED RTLIL::SigBit OrnotGate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, const std::string &src = "");
		SigBit OrnotGate(IdString *name, SigBit *sig_a, SigBit *sig_b, std::string src = "");

		//WRAPPED RTLIL::SigBit MuxGate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, RTLIL::SigBit sig_s, const std::string &src = "");
		SigBit MuxGate(IdString *name, SigBit *sig_a, SigBit *sig_b, SigBit *sig_s, std::string src = "");

		//WRAPPED RTLIL::SigBit Aoi3Gate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, RTLIL::SigBit sig_c, const std::string &src = "");
		SigBit Aoi3Gate(IdString *name, SigBit *sig_a, SigBit *sig_b, SigBit *sig_c, std::string src = "");

		//WRAPPED RTLIL::SigBit Oai3Gate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, RTLIL::SigBit sig_c, const std::string &src = "");
		SigBit Oai3Gate(IdString *name, SigBit *sig_a, SigBit *sig_b, SigBit *sig_c, std::string src = "");

		//WRAPPED RTLIL::SigBit Aoi4Gate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, RTLIL::SigBit sig_c, RTLIL::SigBit sig_d, const std::string &src = "");
		SigBit Aoi4Gate(IdString *name, SigBit *sig_a, SigBit *sig_b, SigBit *sig_c, SigBit *sig_d, std::string src = "");

		//WRAPPED RTLIL::SigBit Oai4Gate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, RTLIL::SigBit sig_c, RTLIL::SigBit sig_d, const std::string &src = "");
		SigBit Oai4Gate(IdString *name, SigBit *sig_a, SigBit *sig_b, SigBit *sig_c, SigBit *sig_d, std::string src = "");

		//WRAPPED RTLIL::SigSpec Anyconst(RTLIL::IdString name, int width = 1, const std::string &src = "");
		SigSpec Anyconst(IdString *name, int width = 1, std::string src = "");

		//WRAPPED RTLIL::SigSpec Anyseq(RTLIL::IdString name, int width = 1, const std::string &src = "");
		SigSpec Anyseq(IdString *name, int width = 1, std::string src = "");

		//WRAPPED RTLIL::SigSpec Allconst(RTLIL::IdString name, int width = 1, const std::string &src = "");
		SigSpec Allconst(IdString *name, int width = 1, std::string src = "");

		//WRAPPED RTLIL::SigSpec Allseq(RTLIL::IdString name, int width = 1, const std::string &src = "");
		SigSpec Allseq(IdString *name, int width = 1, std::string src = "");

		//WRAPPED RTLIL::SigSpec Initstate(RTLIL::IdString name, const std::string &src = "");
		SigSpec Initstate(IdString *name, std::string src = "");
	};

	std::ostream &operator<<(std::ostream &ostr, const Module &ref)
	{
		if(ref.get_cpp_obj() != NULL)
			ostr << "Module with name " << ref.get_cpp_obj()->name.c_str();
		else
			ostr << "deleted Module";
		return ostr;
	}
	//WRAPPED from kernel/rtlil
	struct Design
	{
		unsigned int hashidx_;
		Yosys::RTLIL::Design* ref_obj;

		Design(Yosys::RTLIL::Design* ref = new Yosys::RTLIL::Design())
		{
			this->hashidx_ = ref->hashidx_;
			this->ref_obj = ref;
		}

		Yosys::RTLIL::Design* get_cpp_obj() const
		{
			Yosys::RTLIL::Design* ret = Yosys::RTLIL::Design::get_all_designs()->at(this->hashidx_);
			if(ret != NULL && ret == this->ref_obj)
				return ret;
			return NULL;
		}

		boost::python::list get_modules()
		{
			Yosys::RTLIL::Design* cpp_obj = get_cpp_obj();
			boost::python::list result;
			if(cpp_obj == NULL)
			{
				return result;
			}
			for(auto &mod_it : cpp_obj->modules_)
			{
				result.append(Module(mod_it.second));
			}
			return result;
		}

		void run(std::string command)
		{
			Yosys::RTLIL::Design* cpp_design = get_cpp_obj();
			if(cpp_design != NULL)
				Yosys::run_pass(command, cpp_design);

		}

		void register_monitor(Monitor* const m);

		//WRAPPED unsigned int hash() const { return hashidx_; }
		unsigned int hash();

		//WRAPPED RTLIL::Module *module(RTLIL::IdString name);
		Module module(IdString *name);

		//WRAPPED bool has(RTLIL::IdString id) const {
		bool has(IdString *id);

		//WRAPPED void add(RTLIL::Module *module);
		void add(Module *module);

		//WRAPPED RTLIL::Module *addModule(RTLIL::IdString name);
		Module addModule(IdString *name);

		//WRAPPED void remove(RTLIL::Module *module);
		void remove(Module *module);

		//WRAPPED void rename(RTLIL::Module *module, RTLIL::IdString new_name);
		void rename(Module *module, IdString *new_name);

		//WRAPPED void scratchpad_unset(std::string varname);
		void scratchpad_unset(std::string varname);

		//WRAPPED void scratchpad_set_int(std::string varname, int value);
		void scratchpad_set_int(std::string varname, int value);

		//WRAPPED void scratchpad_set_bool(std::string varname, bool value);
		void scratchpad_set_bool(std::string varname, bool value);

		//WRAPPED void scratchpad_set_string(std::string varname, std::string value);
		void scratchpad_set_string(std::string varname, std::string value);

		//WRAPPED int scratchpad_get_int(std::string varname, int default_value = 0) const;
		int scratchpad_get_int(std::string varname, int default_value = 0);

		//WRAPPED bool scratchpad_get_bool(std::string varname, bool default_value = false) const;
		bool scratchpad_get_bool(std::string varname, bool default_value = false);

		//WRAPPED std::string scratchpad_get_string(std::string varname, std::string default_value = std::string()) const;
		std::string scratchpad_get_string(std::string varname, std::string default_value = std::string());

		//WRAPPED bool selected_module(RTLIL::IdString mod_name) const;
		bool selected_module_IdString(IdString *mod_name);

		//WRAPPED bool selected_whole_module(RTLIL::IdString mod_name) const;
		bool selected_whole_module_IdString(IdString *mod_name);

		//WRAPPED bool selected_member(RTLIL::IdString mod_name, RTLIL::IdString memb_name) const;
		bool selected_member(IdString *mod_name, IdString *memb_name);

		//WRAPPED bool selected_module(RTLIL::Module *mod) const;
		bool selected_module_Module(Module *mod);

		//WRAPPED bool selected_whole_module(RTLIL::Module *mod) const;
		bool selected_whole_module_Module(Module *mod);

		//WRAPPED bool full_selection() const {
		bool full_selection();
	};

	std::ostream &operator<<(std::ostream &ostr, const Design &ref)
	{
		if(ref.get_cpp_obj() != NULL)
			ostr << "Design with identifier " << ref.hashidx_;
		else
			ostr << "deleted Design";
		return ostr;
	}

	//WRAPPED static inline std::string escape_id(std::string str) { FROM FILE kernel/rtlil.h
	inline std::string escape_id(std::string str)
	{
		return Yosys::RTLIL::escape_id(str);
	}

	//WRAPPED static inline std::string unescape_id(std::string str) { FROM FILE kernel/rtlil.h
	inline std::string unescape_id_std_string(std::string str)
	{
		return Yosys::RTLIL::unescape_id(str);
	}

	//WRAPPED static inline std::string unescape_id(RTLIL::IdString str) { FROM FILE kernel/rtlil.h
	inline std::string unescape_id_IdString(IdString *str)
	{
		return Yosys::RTLIL::unescape_id(*str->get_cpp_obj());
	}

	//WRAPPED RTLIL::Const const_not(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len); FROM FILE kernel/rtlil.h
	Const const_not(Const *arg1, Const *arg2, bool signed1, bool signed2, int result_len)
	{
		return Const(Yosys::RTLIL::const_not(*arg1->get_cpp_obj(), *arg2->get_cpp_obj(), signed1, signed2, result_len));
	}

	//WRAPPED RTLIL::Const const_and(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len); FROM FILE kernel/rtlil.h
	Const const_and(Const *arg1, Const *arg2, bool signed1, bool signed2, int result_len)
	{
		return Const(Yosys::RTLIL::const_and(*arg1->get_cpp_obj(), *arg2->get_cpp_obj(), signed1, signed2, result_len));
	}

	//WRAPPED RTLIL::Const const_or(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len); FROM FILE kernel/rtlil.h
	Const const_or(Const *arg1, Const *arg2, bool signed1, bool signed2, int result_len)
	{
		return Const(Yosys::RTLIL::const_or(*arg1->get_cpp_obj(), *arg2->get_cpp_obj(), signed1, signed2, result_len));
	}

	//WRAPPED RTLIL::Const const_xor(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len); FROM FILE kernel/rtlil.h
	Const const_xor(Const *arg1, Const *arg2, bool signed1, bool signed2, int result_len)
	{
		return Const(Yosys::RTLIL::const_xor(*arg1->get_cpp_obj(), *arg2->get_cpp_obj(), signed1, signed2, result_len));
	}

	//WRAPPED RTLIL::Const const_xnor(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len); FROM FILE kernel/rtlil.h
	Const const_xnor(Const *arg1, Const *arg2, bool signed1, bool signed2, int result_len)
	{
		return Const(Yosys::RTLIL::const_xnor(*arg1->get_cpp_obj(), *arg2->get_cpp_obj(), signed1, signed2, result_len));
	}

	//WRAPPED RTLIL::Const const_reduce_and(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len); FROM FILE kernel/rtlil.h
	Const const_reduce_and(Const *arg1, Const *arg2, bool signed1, bool signed2, int result_len)
	{
		return Const(Yosys::RTLIL::const_reduce_and(*arg1->get_cpp_obj(), *arg2->get_cpp_obj(), signed1, signed2, result_len));
	}

	//WRAPPED RTLIL::Const const_reduce_or(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len); FROM FILE kernel/rtlil.h
	Const const_reduce_or(Const *arg1, Const *arg2, bool signed1, bool signed2, int result_len)
	{
		return Const(Yosys::RTLIL::const_reduce_or(*arg1->get_cpp_obj(), *arg2->get_cpp_obj(), signed1, signed2, result_len));
	}

	//WRAPPED RTLIL::Const const_reduce_xor(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len); FROM FILE kernel/rtlil.h
	Const const_reduce_xor(Const *arg1, Const *arg2, bool signed1, bool signed2, int result_len)
	{
		return Const(Yosys::RTLIL::const_reduce_xor(*arg1->get_cpp_obj(), *arg2->get_cpp_obj(), signed1, signed2, result_len));
	}

	//WRAPPED RTLIL::Const const_reduce_xnor(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len); FROM FILE kernel/rtlil.h
	Const const_reduce_xnor(Const *arg1, Const *arg2, bool signed1, bool signed2, int result_len)
	{
		return Const(Yosys::RTLIL::const_reduce_xnor(*arg1->get_cpp_obj(), *arg2->get_cpp_obj(), signed1, signed2, result_len));
	}

	//WRAPPED RTLIL::Const const_reduce_bool(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len); FROM FILE kernel/rtlil.h
	Const const_reduce_bool(Const *arg1, Const *arg2, bool signed1, bool signed2, int result_len)
	{
		return Const(Yosys::RTLIL::const_reduce_bool(*arg1->get_cpp_obj(), *arg2->get_cpp_obj(), signed1, signed2, result_len));
	}

	//WRAPPED RTLIL::Const const_logic_not(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len); FROM FILE kernel/rtlil.h
	Const const_logic_not(Const *arg1, Const *arg2, bool signed1, bool signed2, int result_len)
	{
		return Const(Yosys::RTLIL::const_logic_not(*arg1->get_cpp_obj(), *arg2->get_cpp_obj(), signed1, signed2, result_len));
	}

	//WRAPPED RTLIL::Const const_logic_and(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len); FROM FILE kernel/rtlil.h
	Const const_logic_and(Const *arg1, Const *arg2, bool signed1, bool signed2, int result_len)
	{
		return Const(Yosys::RTLIL::const_logic_and(*arg1->get_cpp_obj(), *arg2->get_cpp_obj(), signed1, signed2, result_len));
	}

	//WRAPPED RTLIL::Const const_logic_or(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len); FROM FILE kernel/rtlil.h
	Const const_logic_or(Const *arg1, Const *arg2, bool signed1, bool signed2, int result_len)
	{
		return Const(Yosys::RTLIL::const_logic_or(*arg1->get_cpp_obj(), *arg2->get_cpp_obj(), signed1, signed2, result_len));
	}

	//WRAPPED RTLIL::Const const_shl(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len); FROM FILE kernel/rtlil.h
	Const const_shl(Const *arg1, Const *arg2, bool signed1, bool signed2, int result_len)
	{
		return Const(Yosys::RTLIL::const_shl(*arg1->get_cpp_obj(), *arg2->get_cpp_obj(), signed1, signed2, result_len));
	}

	//WRAPPED RTLIL::Const const_shr(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len); FROM FILE kernel/rtlil.h
	Const const_shr(Const *arg1, Const *arg2, bool signed1, bool signed2, int result_len)
	{
		return Const(Yosys::RTLIL::const_shr(*arg1->get_cpp_obj(), *arg2->get_cpp_obj(), signed1, signed2, result_len));
	}

	//WRAPPED RTLIL::Const const_sshl(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len); FROM FILE kernel/rtlil.h
	Const const_sshl(Const *arg1, Const *arg2, bool signed1, bool signed2, int result_len)
	{
		return Const(Yosys::RTLIL::const_sshl(*arg1->get_cpp_obj(), *arg2->get_cpp_obj(), signed1, signed2, result_len));
	}

	//WRAPPED RTLIL::Const const_sshr(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len); FROM FILE kernel/rtlil.h
	Const const_sshr(Const *arg1, Const *arg2, bool signed1, bool signed2, int result_len)
	{
		return Const(Yosys::RTLIL::const_sshr(*arg1->get_cpp_obj(), *arg2->get_cpp_obj(), signed1, signed2, result_len));
	}

	//WRAPPED RTLIL::Const const_shift(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len); FROM FILE kernel/rtlil.h
	Const const_shift(Const *arg1, Const *arg2, bool signed1, bool signed2, int result_len)
	{
		return Const(Yosys::RTLIL::const_shift(*arg1->get_cpp_obj(), *arg2->get_cpp_obj(), signed1, signed2, result_len));
	}

	//WRAPPED RTLIL::Const const_shiftx(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len); FROM FILE kernel/rtlil.h
	Const const_shiftx(Const *arg1, Const *arg2, bool signed1, bool signed2, int result_len)
	{
		return Const(Yosys::RTLIL::const_shiftx(*arg1->get_cpp_obj(), *arg2->get_cpp_obj(), signed1, signed2, result_len));
	}

	//WRAPPED RTLIL::Const const_lt(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len); FROM FILE kernel/rtlil.h
	Const const_lt(Const *arg1, Const *arg2, bool signed1, bool signed2, int result_len)
	{
		return Const(Yosys::RTLIL::const_lt(*arg1->get_cpp_obj(), *arg2->get_cpp_obj(), signed1, signed2, result_len));
	}

	//WRAPPED RTLIL::Const const_le(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len); FROM FILE kernel/rtlil.h
	Const const_le(Const *arg1, Const *arg2, bool signed1, bool signed2, int result_len)
	{
		return Const(Yosys::RTLIL::const_le(*arg1->get_cpp_obj(), *arg2->get_cpp_obj(), signed1, signed2, result_len));
	}

	//WRAPPED RTLIL::Const const_eq(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len); FROM FILE kernel/rtlil.h
	Const const_eq(Const *arg1, Const *arg2, bool signed1, bool signed2, int result_len)
	{
		return Const(Yosys::RTLIL::const_eq(*arg1->get_cpp_obj(), *arg2->get_cpp_obj(), signed1, signed2, result_len));
	}

	//WRAPPED RTLIL::Const const_ne(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len); FROM FILE kernel/rtlil.h
	Const const_ne(Const *arg1, Const *arg2, bool signed1, bool signed2, int result_len)
	{
		return Const(Yosys::RTLIL::const_ne(*arg1->get_cpp_obj(), *arg2->get_cpp_obj(), signed1, signed2, result_len));
	}

	//WRAPPED RTLIL::Const const_eqx(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len); FROM FILE kernel/rtlil.h
	Const const_eqx(Const *arg1, Const *arg2, bool signed1, bool signed2, int result_len)
	{
		return Const(Yosys::RTLIL::const_eqx(*arg1->get_cpp_obj(), *arg2->get_cpp_obj(), signed1, signed2, result_len));
	}

	//WRAPPED RTLIL::Const const_nex(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len); FROM FILE kernel/rtlil.h
	Const const_nex(Const *arg1, Const *arg2, bool signed1, bool signed2, int result_len)
	{
		return Const(Yosys::RTLIL::const_nex(*arg1->get_cpp_obj(), *arg2->get_cpp_obj(), signed1, signed2, result_len));
	}

	//WRAPPED RTLIL::Const const_ge(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len); FROM FILE kernel/rtlil.h
	Const const_ge(Const *arg1, Const *arg2, bool signed1, bool signed2, int result_len)
	{
		return Const(Yosys::RTLIL::const_ge(*arg1->get_cpp_obj(), *arg2->get_cpp_obj(), signed1, signed2, result_len));
	}

	//WRAPPED RTLIL::Const const_gt(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len); FROM FILE kernel/rtlil.h
	Const const_gt(Const *arg1, Const *arg2, bool signed1, bool signed2, int result_len)
	{
		return Const(Yosys::RTLIL::const_gt(*arg1->get_cpp_obj(), *arg2->get_cpp_obj(), signed1, signed2, result_len));
	}

	//WRAPPED RTLIL::Const const_add(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len); FROM FILE kernel/rtlil.h
	Const const_add(Const *arg1, Const *arg2, bool signed1, bool signed2, int result_len)
	{
		return Const(Yosys::RTLIL::const_add(*arg1->get_cpp_obj(), *arg2->get_cpp_obj(), signed1, signed2, result_len));
	}

	//WRAPPED RTLIL::Const const_sub(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len); FROM FILE kernel/rtlil.h
	Const const_sub(Const *arg1, Const *arg2, bool signed1, bool signed2, int result_len)
	{
		return Const(Yosys::RTLIL::const_sub(*arg1->get_cpp_obj(), *arg2->get_cpp_obj(), signed1, signed2, result_len));
	}

	//WRAPPED RTLIL::Const const_mul(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len); FROM FILE kernel/rtlil.h
	Const const_mul(Const *arg1, Const *arg2, bool signed1, bool signed2, int result_len)
	{
		return Const(Yosys::RTLIL::const_mul(*arg1->get_cpp_obj(), *arg2->get_cpp_obj(), signed1, signed2, result_len));
	}

	//WRAPPED RTLIL::Const const_div(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len); FROM FILE kernel/rtlil.h
	Const const_div(Const *arg1, Const *arg2, bool signed1, bool signed2, int result_len)
	{
		return Const(Yosys::RTLIL::const_div(*arg1->get_cpp_obj(), *arg2->get_cpp_obj(), signed1, signed2, result_len));
	}

	//WRAPPED RTLIL::Const const_mod(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len); FROM FILE kernel/rtlil.h
	Const const_mod(Const *arg1, Const *arg2, bool signed1, bool signed2, int result_len)
	{
		return Const(Yosys::RTLIL::const_mod(*arg1->get_cpp_obj(), *arg2->get_cpp_obj(), signed1, signed2, result_len));
	}

	//WRAPPED RTLIL::Const const_pow(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len); FROM FILE kernel/rtlil.h
	Const const_pow(Const *arg1, Const *arg2, bool signed1, bool signed2, int result_len)
	{
		return Const(Yosys::RTLIL::const_pow(*arg1->get_cpp_obj(), *arg2->get_cpp_obj(), signed1, signed2, result_len));
	}

	//WRAPPED RTLIL::Const const_pos(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len); FROM FILE kernel/rtlil.h
	Const const_pos(Const *arg1, Const *arg2, bool signed1, bool signed2, int result_len)
	{
		return Const(Yosys::RTLIL::const_pos(*arg1->get_cpp_obj(), *arg2->get_cpp_obj(), signed1, signed2, result_len));
	}

	//WRAPPED RTLIL::Const const_neg(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len); FROM FILE kernel/rtlil.h
	Const const_neg(Const *arg1, Const *arg2, bool signed1, bool signed2, int result_len)
	{
		return Const(Yosys::RTLIL::const_neg(*arg1->get_cpp_obj(), *arg2->get_cpp_obj(), signed1, signed2, result_len));
	}

	struct Monitor : public Yosys::RTLIL::Monitor
	{

		virtual void notify_module_add(Yosys::RTLIL::Module *module) YS_OVERRIDE
		{
			py_notify_module_add(Module(module));
		}

		virtual void notify_module_del(Yosys::RTLIL::Module *module) YS_OVERRIDE
		{
			py_notify_module_del(Module(module));
		}

		virtual void notify_connect(Yosys::RTLIL::Cell *cell, const Yosys::RTLIL::IdString &port, const Yosys::RTLIL::SigSpec &old_sig, Yosys::RTLIL::SigSpec &sig) YS_OVERRIDE
		{
			Yosys::RTLIL::IdString *tmp_port = new Yosys::RTLIL::IdString(port);
			Yosys::RTLIL::SigSpec *tmp_old_sig = new Yosys::RTLIL::SigSpec(old_sig);
			py_notify_connect_cell(Cell(cell), IdString(tmp_port), SigSpec(tmp_old_sig), SigSpec(&sig));
		}

		virtual void notify_connect(Yosys::RTLIL::Module *module, const Yosys::RTLIL::SigSig &sigsig) YS_OVERRIDE
		{
			Yosys::RTLIL::SigSpec *first = new Yosys::RTLIL::SigSpec(sigsig.first);
			Yosys::RTLIL::SigSpec *second = new Yosys::RTLIL::SigSpec(sigsig.second);
			py_notify_connect_tuple(Module(module), boost::python::make_tuple(SigSpec(first), SigSpec(second)));
		}

		virtual void notify_connect(Yosys::RTLIL::Module *module, const std::vector<Yosys::RTLIL::SigSig> &sigsig_vec) YS_OVERRIDE
		{
			boost::python::list sigsig_list;
			for(auto sigsig : sigsig_vec)
				sigsig_list.append(boost::python::make_tuple(*(new SigSpec(&sigsig.first)), *(new SigSpec(&sigsig.second))));
			py_notify_connect_list(Module(module), sigsig_list);
		}

		virtual void notify_blackout(Yosys::RTLIL::Module *module) YS_OVERRIDE
		{
			py_notify_blackout(Module(module));
		}

		virtual void py_notify_module_add(Module){};
		virtual void py_notify_module_del(Module){};
		virtual void py_notify_connect_cell(Cell cell, IdString port, SigSpec old_sig, SigSpec sig){};
		virtual void py_notify_connect_tuple(Module module, boost::python::tuple sigsig){};
		virtual void py_notify_connect_list(Module module, boost::python::list sigsig_list){};
		virtual void py_notify_blackout(Module){};
	};

	struct MonitorWrap : Monitor, boost::python::wrapper<Monitor>
	{
		void py_notify_module_add(Module m)
		{
			if(boost::python::override py_notify_module_add = this->get_override("py_notify_module_add"))
				py_notify_module_add(m);
			else
				Monitor::py_notify_module_add(m);
		}

		void default_py_notify_module_add(Module m)
		{
			this->Monitor::py_notify_module_add(m);
		}

		void py_notify_module_del(Module m)
		{
			if(boost::python::override py_notify_module_del = this->get_override("py_notify_module_del"))
				py_notify_module_del(m);
		else
				Monitor::py_notify_module_del(m);
		}

		void default_py_notify_module_del(Module m)
		{
			this->Monitor::py_notify_module_del(m);
		}

		void py_notify_connect_cell(Cell cell, IdString port, SigSpec old_sig, SigSpec sig)
		{
			if(boost::python::override py_notify_connect_cell = this->get_override("py_notify_connect_cell"))
				py_notify_connect_cell(cell, port, old_sig, sig);
			else
				Monitor::py_notify_connect_cell(cell, port, old_sig, sig);
		}

		void default_py_notify_connect_cell(Cell cell, IdString port, SigSpec old_sig, SigSpec sig)
		{
			this->Monitor::py_notify_connect_cell(cell, port, old_sig, sig);
		}

		void py_notify_connect_tuple(Module module, boost::python::tuple sigsig)
		{
			if(boost::python::override py_notify_connect_tuple = this->get_override("py_notify_connect_tuple"))
				py_notify_connect_tuple(module, sigsig);
			else
				Monitor::py_notify_connect_tuple(module, sigsig);
		}

		void default_py_notify_connect_tuple(Module module, boost::python::tuple sigsig)
		{
			this->Monitor::py_notify_connect_tuple(module, sigsig);
		}

		void py_notify_connect_list(Module module, boost::python::list sigsig_list)
		{
			if(boost::python::override py_notify_connect_list = this->get_override("py_notify_connect_list"))
				py_notify_connect_list(module, sigsig_list);
			else
				Monitor::py_notify_connect_list(module, sigsig_list);
		}

		void default_py_notify_connect_list(Module module, boost::python::list sigsig_list)
		{
			this->Monitor::py_notify_connect_list(module, sigsig_list);
		}

		void py_notify_blackout(Module m)
		{
			if(boost::python::override py_notify_blackout = this->get_override("py_notify_blackout"))
				py_notify_blackout(m);
			else
				Monitor::py_notify_blackout(m);
		}

		void default_py_notify_blackout(Module m)
		{
			this->Monitor::py_notify_blackout(m);
		}
	};

	struct PyPass : public Yosys::Pass
	{
		PyPass(std::string name, std::string short_help) : Yosys::Pass(name, short_help) { }
	
		virtual void execute(vector<string> args, Yosys::RTLIL::Design* d)  YS_OVERRIDE
		{
			boost::python::list py_args;
			for(auto arg : args)
				py_args.append(arg);
			py_execute(py_args, new Design(d));
		}

		virtual void help() YS_OVERRIDE
		{
			py_help();
		}

		virtual void py_execute(boost::python::list args, Design* d){}
		virtual void py_help(){}
	};

	struct PassWrap : PyPass, boost::python::wrapper<PyPass>
	{

		PassWrap(std::string name, std::string short_help) : PyPass(name, short_help) { }
	
		void py_execute(boost::python::list args, Design* d)
		{
			if(boost::python::override py_execute = this->get_override("py_execute"))
				py_execute(args, d);
			else
				PyPass::py_execute(args, d);
		}

		void default_py_execute(boost::python::list args, Design* d)
		{
			this->PyPass::py_execute(args, d);
		}

		void py_help()
		{
			if(boost::python::override py_help = this->get_override("py_help"))
				py_help();
			else
				PyPass::py_help();
		}

		void default_py_help()
		{
			this->PyPass::py_help();
		}
	};

	void Module::register_monitor(Monitor* const m)
	{
		Yosys::RTLIL::Module* cpp_module = this->get_cpp_obj();
		if(cpp_module == NULL)
			return;
		cpp_module->monitors.insert(m);
	}

	void Design::register_monitor(Monitor* const m)
	{
		Yosys::RTLIL::Design* cpp_design = this->get_cpp_obj();
		if(cpp_design == NULL)
			return;
		cpp_design->monitors.insert(m);
	}

	//WRAPPED static inline int get_reference(int idx) FROM FILE kernel/rtlil.h
	inline int IdString::get_reference(int idx)
	{
		return Yosys::RTLIL::IdString::get_reference(idx);
	}

	//WRAPPED static inline void put_reference(int idx) FROM FILE kernel/rtlil.h
	inline void IdString::put_reference(int idx)
	{
		Yosys::RTLIL::IdString::put_reference(idx);
	}

	//WRAPPED std::string str() const { FROM FILE kernel/rtlil.h
	std::string IdString::str()
	{
		return this->get_cpp_obj()->str();
	}

	//WRAPPED std::string substr(size_t pos = 0, size_t len = std::string::npos) const { FROM FILE kernel/rtlil.h
	std::string IdString::substr(size_t pos, size_t len)
	{
		return this->get_cpp_obj()->substr(pos, len);
	}

	//WRAPPED size_t size() const { FROM FILE kernel/rtlil.h
	size_t IdString::size()
	{
		return this->get_cpp_obj()->size();
	}

	//WRAPPED bool empty() const { FROM FILE kernel/rtlil.h
	bool IdString::empty()
	{
		return this->get_cpp_obj()->empty();
	}

	//WRAPPED void clear() { FROM FILE kernel/rtlil.h
	void IdString::clear()
	{
		this->get_cpp_obj()->clear();
	}

	//WRAPPED unsigned int hash() const { FROM FILE kernel/rtlil.h
	unsigned int IdString::hash()
	{
		return this->get_cpp_obj()->hash();
	}

	//WRAPPED bool in(IdString rhs) const { return *this == rhs; } FROM FILE kernel/rtlil.h
	bool IdString::in_IdString(IdString *rhs)
	{
		return this->get_cpp_obj()->in(*rhs->get_cpp_obj());
	}

	//WRAPPED bool in(const std::string &rhs) const { return *this == rhs; } FROM FILE kernel/rtlil.h
	bool IdString::in_std_string(std::string rhs)
	{
		return this->get_cpp_obj()->in(rhs);
	}

	//WRAPPED bool in(const pool<IdString> &rhs) const { return rhs.count(*this) != 0; } FROM FILE kernel/rtlil.h
	bool IdString::in_pool_IdString(boost::python::list rhs)
	{
		pool<Yosys::RTLIL::IdString> rhs_;
		while(len(rhs) > 0)
		{
			IdString tmp = boost::python::extract<IdString>(rhs.pop());
			rhs_.insert(*tmp.get_cpp_obj());
		}
		return this->get_cpp_obj()->in(rhs_);
	}

	//WRAPPED bool as_bool() const; FROM FILE kernel/rtlil.h
	bool Const::as_bool()
	{
		return this->get_cpp_obj()->as_bool();
	}

	//WRAPPED int as_int(bool is_signed = false) const; FROM FILE kernel/rtlil.h
	int Const::as_int(bool is_signed)
	{
		return this->get_cpp_obj()->as_int(is_signed);
	}

	//WRAPPED std::string as_string() const; FROM FILE kernel/rtlil.h
	std::string Const::as_string()
	{
		return this->get_cpp_obj()->as_string();
	}

	//WRAPPED static Const from_string(std::string str); FROM FILE kernel/rtlil.h
	Const Const::from_string(std::string str)
	{
		return Const(Yosys::RTLIL::Const::from_string(str));
	}

	//WRAPPED std::string decode_string() const; FROM FILE kernel/rtlil.h
	std::string Const::decode_string()
	{
		return this->get_cpp_obj()->decode_string();
	}

	//WRAPPED inline int size() const { return bits.size(); } FROM FILE kernel/rtlil.h
	inline int Const::size()
	{
		return this->get_cpp_obj()->size();
	}

	//WRAPPED bool is_fully_zero() const; FROM FILE kernel/rtlil.h
	bool Const::is_fully_zero()
	{
		return this->get_cpp_obj()->is_fully_zero();
	}

	//WRAPPED bool is_fully_ones() const; FROM FILE kernel/rtlil.h
	bool Const::is_fully_ones()
	{
		return this->get_cpp_obj()->is_fully_ones();
	}

	//WRAPPED bool is_fully_def() const; FROM FILE kernel/rtlil.h
	bool Const::is_fully_def()
	{
		return this->get_cpp_obj()->is_fully_def();
	}

	//WRAPPED bool is_fully_undef() const; FROM FILE kernel/rtlil.h
	bool Const::is_fully_undef()
	{
		return this->get_cpp_obj()->is_fully_undef();
	}

	//WRAPPED inline RTLIL::Const extract(int offset, int len = 1, RTLIL::State padding = RTLIL::State::S0) const { FROM FILE kernel/rtlil.h
	inline Const Const::extract(int offset, int len, State padding)
	{
		return Const(this->get_cpp_obj()->extract(offset, len, padding));
	}

	//WRAPPED inline unsigned int hash() const { FROM FILE kernel/rtlil.h
	inline unsigned int Const::hash()
	{
		return this->get_cpp_obj()->hash();
	}

	//WRAPPED RTLIL::CaseRule *clone() const; FROM FILE kernel/rtlil.h
	CaseRule CaseRule::clone()
	{
		return CaseRule(this->get_cpp_obj()->clone());
	}

	//WRAPPED RTLIL::SwitchRule *clone() const; FROM FILE kernel/rtlil.h
	SwitchRule SwitchRule::clone()
	{
		return SwitchRule(this->get_cpp_obj()->clone());
	}

	//WRAPPED RTLIL::SyncRule *clone() const; FROM FILE kernel/rtlil.h
	SyncRule SyncRule::clone()
	{
		return SyncRule(this->get_cpp_obj()->clone());
	}

	//WRAPPED RTLIL::Process *clone() const; FROM FILE kernel/rtlil.h
	Process Process::clone()
	{
		return Process(this->get_cpp_obj()->clone());
	}

	//WRAPPED RTLIL::SigChunk extract(int offset, int length) const; FROM FILE kernel/rtlil.h
	SigChunk SigChunk::extract(int offset, int length)
	{
		return SigChunk(this->get_cpp_obj()->extract(offset, length));
	}

	//WRAPPED unsigned int hash() const; FROM FILE kernel/rtlil.h
	unsigned int SigBit::hash()
	{
		return this->get_cpp_obj()->hash();
	}

	//WRAPPED size_t get_hash() const { FROM FILE kernel/rtlil.h
	size_t SigSpec::get_hash()
	{
		return this->get_cpp_obj()->get_hash();
	}

	//WRAPPED inline int size() const { return width_; } FROM FILE kernel/rtlil.h
	inline int SigSpec::size()
	{
		return this->get_cpp_obj()->size();
	}

	//WRAPPED inline bool empty() const { return width_ == 0; } FROM FILE kernel/rtlil.h
	inline bool SigSpec::empty()
	{
		return this->get_cpp_obj()->empty();
	}

	//WRAPPED void replace(const RTLIL::SigSpec &pattern, const RTLIL::SigSpec &with); FROM FILE kernel/rtlil.h
	void SigSpec::replace_SigSpec_SigSpec(SigSpec *pattern, SigSpec *with)
	{
		this->get_cpp_obj()->replace(*pattern->get_cpp_obj(), *with->get_cpp_obj());
	}

	//WRAPPED void replace(const RTLIL::SigSpec &pattern, const RTLIL::SigSpec &with, RTLIL::SigSpec *other) const; FROM FILE kernel/rtlil.h
	void SigSpec::replace_SigSpec_SigSpec_SigSpec(SigSpec *pattern, SigSpec *with, SigSpec *other)
	{
		this->get_cpp_obj()->replace(*pattern->get_cpp_obj(), *with->get_cpp_obj(), other->get_cpp_obj());
	}

	//WRAPPED void replace(int offset, const RTLIL::SigSpec &with); FROM FILE kernel/rtlil.h
	void SigSpec::replace_int_SigSpec(int offset, SigSpec *with)
	{
		this->get_cpp_obj()->replace(offset, *with->get_cpp_obj());
	}

	//WRAPPED void remove(const RTLIL::SigSpec &pattern); FROM FILE kernel/rtlil.h
	void SigSpec::remove_SigSpec(SigSpec *pattern)
	{
		this->get_cpp_obj()->remove(*pattern->get_cpp_obj());
	}

	//WRAPPED void remove(const RTLIL::SigSpec &pattern, RTLIL::SigSpec *other) const; FROM FILE kernel/rtlil.h
	void SigSpec::remove_SigSpec_SigSpec(SigSpec *pattern, SigSpec *other)
	{
		this->get_cpp_obj()->remove(*pattern->get_cpp_obj(), other->get_cpp_obj());
	}

	//WRAPPED void remove2(const RTLIL::SigSpec &pattern, RTLIL::SigSpec *other); FROM FILE kernel/rtlil.h
	void SigSpec::remove2_SigSpec_SigSpec(SigSpec *pattern, SigSpec *other)
	{
		this->get_cpp_obj()->remove2(*pattern->get_cpp_obj(), other->get_cpp_obj());
	}

	//WRAPPED void remove(const pool<RTLIL::SigBit> &pattern); FROM FILE kernel/rtlil.h
	void SigSpec::remove_pool_SigBit(boost::python::list pattern)
	{
		pool<Yosys::RTLIL::SigBit> pattern_;
		while(len(pattern) > 0)
		{
			SigBit tmp = boost::python::extract<SigBit>(pattern.pop());
			pattern_.insert(*tmp.get_cpp_obj());
		}
		this->get_cpp_obj()->remove(pattern_);
	}

	//WRAPPED void remove(const pool<RTLIL::SigBit> &pattern, RTLIL::SigSpec *other) const; FROM FILE kernel/rtlil.h
	void SigSpec::remove_pool_SigBit_SigSpec(boost::python::list pattern, SigSpec *other)
	{
		pool<Yosys::RTLIL::SigBit> pattern_;
		while(len(pattern) > 0)
		{
			SigBit tmp = boost::python::extract<SigBit>(pattern.pop());
			pattern_.insert(*tmp.get_cpp_obj());
		}
		this->get_cpp_obj()->remove(pattern_, other->get_cpp_obj());
	}

	//WRAPPED void remove2(const pool<RTLIL::SigBit> &pattern, RTLIL::SigSpec *other); FROM FILE kernel/rtlil.h
	void SigSpec::remove2_pool_SigBit_SigSpec(boost::python::list pattern, SigSpec *other)
	{
		pool<Yosys::RTLIL::SigBit> pattern_;
		while(len(pattern) > 0)
		{
			SigBit tmp = boost::python::extract<SigBit>(pattern.pop());
			pattern_.insert(*tmp.get_cpp_obj());
		}
		this->get_cpp_obj()->remove2(pattern_, other->get_cpp_obj());
	}

	//WRAPPED void remove(int offset, int length = 1); FROM FILE kernel/rtlil.h
	void SigSpec::remove_int_int(int offset, int length)
	{
		this->get_cpp_obj()->remove(offset, length);
	}

	//WRAPPED RTLIL::SigSpec extract(const RTLIL::SigSpec &pattern, const RTLIL::SigSpec *other = NULL) const; FROM FILE kernel/rtlil.h
	SigSpec SigSpec::extract_SigSpec_SigSpec(SigSpec *pattern, SigSpec *other)
	{
		return SigSpec(this->get_cpp_obj()->extract(*pattern->get_cpp_obj(), other->get_cpp_obj()));
	}

	//WRAPPED RTLIL::SigSpec extract(const pool<RTLIL::SigBit> &pattern, const RTLIL::SigSpec *other = NULL) const; FROM FILE kernel/rtlil.h
	SigSpec SigSpec::extract_pool_SigBit_SigSpec(boost::python::list pattern, SigSpec *other)
	{
		pool<Yosys::RTLIL::SigBit> pattern_;
		while(len(pattern) > 0)
		{
			SigBit tmp = boost::python::extract<SigBit>(pattern.pop());
			pattern_.insert(*tmp.get_cpp_obj());
		}
		return SigSpec(this->get_cpp_obj()->extract(pattern_, other->get_cpp_obj()));
	}

	//WRAPPED RTLIL::SigSpec extract(int offset, int length = 1) const; FROM FILE kernel/rtlil.h
	SigSpec SigSpec::extract_int_int(int offset, int length)
	{
		return SigSpec(this->get_cpp_obj()->extract(offset, length));
	}

	//WRAPPED void append(const RTLIL::SigSpec &signal); FROM FILE kernel/rtlil.h
	void SigSpec::append(SigSpec *signal)
	{
		this->get_cpp_obj()->append(*signal->get_cpp_obj());
	}

	//WRAPPED void append_bit(const RTLIL::SigBit &bit); FROM FILE kernel/rtlil.h
	void SigSpec::append_bit(SigBit *bit)
	{
		this->get_cpp_obj()->append_bit(*bit->get_cpp_obj());
	}

	//WRAPPED void extend_u0(int width, bool is_signed = false); FROM FILE kernel/rtlil.h
	void SigSpec::extend_u0(int width, bool is_signed)
	{
		this->get_cpp_obj()->extend_u0(width, is_signed);
	}

	//WRAPPED RTLIL::SigSpec repeat(int num) const; FROM FILE kernel/rtlil.h
	SigSpec SigSpec::repeat(int num)
	{
		return SigSpec(this->get_cpp_obj()->repeat(num));
	}

	//WRAPPED bool is_wire() const; FROM FILE kernel/rtlil.h
	bool SigSpec::is_wire()
	{
		return this->get_cpp_obj()->is_wire();
	}

	//WRAPPED bool is_chunk() const; FROM FILE kernel/rtlil.h
	bool SigSpec::is_chunk()
	{
		return this->get_cpp_obj()->is_chunk();
	}

	//WRAPPED inline bool is_bit() const { return width_ == 1; } FROM FILE kernel/rtlil.h
	inline bool SigSpec::is_bit()
	{
		return this->get_cpp_obj()->is_bit();
	}

	//WRAPPED bool is_fully_const() const; FROM FILE kernel/rtlil.h
	bool SigSpec::is_fully_const()
	{
		return this->get_cpp_obj()->is_fully_const();
	}

	//WRAPPED bool is_fully_zero() const; FROM FILE kernel/rtlil.h
	bool SigSpec::is_fully_zero()
	{
		return this->get_cpp_obj()->is_fully_zero();
	}

	//WRAPPED bool is_fully_ones() const; FROM FILE kernel/rtlil.h
	bool SigSpec::is_fully_ones()
	{
		return this->get_cpp_obj()->is_fully_ones();
	}

	//WRAPPED bool is_fully_def() const; FROM FILE kernel/rtlil.h
	bool SigSpec::is_fully_def()
	{
		return this->get_cpp_obj()->is_fully_def();
	}

	//WRAPPED bool is_fully_undef() const; FROM FILE kernel/rtlil.h
	bool SigSpec::is_fully_undef()
	{
		return this->get_cpp_obj()->is_fully_undef();
	}

	//WRAPPED bool has_const() const; FROM FILE kernel/rtlil.h
	bool SigSpec::has_const()
	{
		return this->get_cpp_obj()->has_const();
	}

	//WRAPPED bool has_marked_bits() const; FROM FILE kernel/rtlil.h
	bool SigSpec::has_marked_bits()
	{
		return this->get_cpp_obj()->has_marked_bits();
	}

	//WRAPPED bool as_bool() const; FROM FILE kernel/rtlil.h
	bool SigSpec::as_bool()
	{
		return this->get_cpp_obj()->as_bool();
	}

	//WRAPPED int as_int(bool is_signed = false) const; FROM FILE kernel/rtlil.h
	int SigSpec::as_int(bool is_signed)
	{
		return this->get_cpp_obj()->as_int(is_signed);
	}

	//WRAPPED std::string as_string() const; FROM FILE kernel/rtlil.h
	std::string SigSpec::as_string()
	{
		return this->get_cpp_obj()->as_string();
	}

	//WRAPPED RTLIL::Const as_const() const; FROM FILE kernel/rtlil.h
	Const SigSpec::as_const()
	{
		return Const(this->get_cpp_obj()->as_const());
	}

	//WRAPPED RTLIL::Wire *as_wire() const; FROM FILE kernel/rtlil.h
	Wire SigSpec::as_wire()
	{
		return Wire(this->get_cpp_obj()->as_wire());
	}

	//WRAPPED RTLIL::SigChunk as_chunk() const; FROM FILE kernel/rtlil.h
	SigChunk SigSpec::as_chunk()
	{
		return SigChunk(this->get_cpp_obj()->as_chunk());
	}

	//WRAPPED RTLIL::SigBit as_bit() const; FROM FILE kernel/rtlil.h
	SigBit SigSpec::as_bit()
	{
		return SigBit(this->get_cpp_obj()->as_bit());
	}

	//WRAPPED bool match(std::string pattern) const; FROM FILE kernel/rtlil.h
	bool SigSpec::match(std::string pattern)
	{
		return this->get_cpp_obj()->match(pattern);
	}

	//WRAPPED static bool parse(RTLIL::SigSpec &sig, RTLIL::Module *module, std::string str); FROM FILE kernel/rtlil.h
	bool SigSpec::parse(SigSpec *sig, Module *module, std::string str)
	{
		return Yosys::RTLIL::SigSpec::parse(*sig->get_cpp_obj(), module->get_cpp_obj(), str);
	}

	//WRAPPED static bool parse_sel(RTLIL::SigSpec &sig, RTLIL::Design *design, RTLIL::Module *module, std::string str); FROM FILE kernel/rtlil.h
	bool SigSpec::parse_sel(SigSpec *sig, Design *design, Module *module, std::string str)
	{
		return Yosys::RTLIL::SigSpec::parse_sel(*sig->get_cpp_obj(), design->get_cpp_obj(), module->get_cpp_obj(), str);
	}

	//WRAPPED static bool parse_rhs(const RTLIL::SigSpec &lhs, RTLIL::SigSpec &sig, RTLIL::Module *module, std::string str); FROM FILE kernel/rtlil.h
	bool SigSpec::parse_rhs(SigSpec *lhs, SigSpec *sig, Module *module, std::string str)
	{
		return Yosys::RTLIL::SigSpec::parse_rhs(*lhs->get_cpp_obj(), *sig->get_cpp_obj(), module->get_cpp_obj(), str);
	}

	//WRAPPED unsigned int hash() const { if(!hash_) updhash(); return hash_; }; FROM FILE kernel/rtlil.h
	unsigned int SigSpec::hash()
	{
		return this->get_cpp_obj()->hash();
	}

	//WRAPPED void check() const; FROM FILE kernel/rtlil.h
	void SigSpec::check()
	{
		this->get_cpp_obj()->check();
	}

	//WRAPPED unsigned int hash() const { return hashidx_; } FROM FILE kernel/rtlil.h
	unsigned int Cell::hash()
	{
		return this->get_cpp_obj()->hash();
	}

	//WRAPPED bool hasPort(RTLIL::IdString portname) const; FROM FILE kernel/rtlil.h
	bool Cell::hasPort(IdString *portname)
	{
		return this->get_cpp_obj()->hasPort(*portname->get_cpp_obj());
	}

	//WRAPPED void unsetPort(RTLIL::IdString portname); FROM FILE kernel/rtlil.h
	void Cell::unsetPort(IdString *portname)
	{
		this->get_cpp_obj()->unsetPort(*portname->get_cpp_obj());
	}

	//WRAPPED void setPort(RTLIL::IdString portname, RTLIL::SigSpec signal); FROM FILE kernel/rtlil.h
	void Cell::setPort(IdString *portname, SigSpec *signal)
	{
		this->get_cpp_obj()->setPort(*portname->get_cpp_obj(), *signal->get_cpp_obj());
	}

	//WRAPPED bool known() const; FROM FILE kernel/rtlil.h
	bool Cell::known()
	{
		return this->get_cpp_obj()->known();
	}

	//WRAPPED bool input(RTLIL::IdString portname) const; FROM FILE kernel/rtlil.h
	bool Cell::input(IdString *portname)
	{
		return this->get_cpp_obj()->input(*portname->get_cpp_obj());
	}

	//WRAPPED bool output(RTLIL::IdString portname) const; FROM FILE kernel/rtlil.h
	bool Cell::output(IdString *portname)
	{
		return this->get_cpp_obj()->output(*portname->get_cpp_obj());
	}

	//WRAPPED bool hasParam(RTLIL::IdString paramname) const; FROM FILE kernel/rtlil.h
	bool Cell::hasParam(IdString *paramname)
	{
		return this->get_cpp_obj()->hasParam(*paramname->get_cpp_obj());
	}

	//WRAPPED void unsetParam(RTLIL::IdString paramname); FROM FILE kernel/rtlil.h
	void Cell::unsetParam(IdString *paramname)
	{
		this->get_cpp_obj()->unsetParam(*paramname->get_cpp_obj());
	}

	//WRAPPED void setParam(RTLIL::IdString paramname, RTLIL::Const value); FROM FILE kernel/rtlil.h
	void Cell::setParam(IdString *paramname, Const *value)
	{
		this->get_cpp_obj()->setParam(*paramname->get_cpp_obj(), *value->get_cpp_obj());
	}

	//WRAPPED void fixup_parameters(bool set_a_signed = false, bool set_b_signed = false); FROM FILE kernel/rtlil.h
	void Cell::fixup_parameters(bool set_a_signed, bool set_b_signed)
	{
		this->get_cpp_obj()->fixup_parameters(set_a_signed, set_b_signed);
	}

	//WRAPPED bool has_keep_attr() const { FROM FILE kernel/rtlil.h
	bool Cell::has_keep_attr()
	{
		return this->get_cpp_obj()->has_keep_attr();
	}

	//WRAPPED unsigned int hash() const { return hashidx_; } FROM FILE kernel/rtlil.h
	unsigned int Wire::hash()
	{
		return this->get_cpp_obj()->hash();
	}

	//WRAPPED unsigned int hash() const { return hashidx_; } FROM FILE kernel/rtlil.h
	unsigned int Memory::hash()
	{
		return this->get_cpp_obj()->hash();
	}

	//WRAPPED unsigned int hash() const { return hashidx_; } FROM FILE kernel/rtlil.h
	unsigned int Module::hash()
	{
		return this->get_cpp_obj()->hash();
	}

	//WRAPPED void connect(const RTLIL::SigSig &conn); FROM FILE kernel/rtlil.h
	void Module::connect_SigSig(PyObject* conn)
	{
		if(!PyTuple_Check(conn) or PyTuple_Size(conn) != 2)
			throw std::logic_error("Tuple of two SigSpecs required");
		SigSpec conn_sp0 = boost::python::extract<SigSpec>(PyTuple_GetItem(conn, 0));
		SigSpec conn_sp1 = boost::python::extract<SigSpec>(PyTuple_GetItem(conn, 1));
		Yosys::RTLIL::SigSig conn_(conn_sp0.get_cpp_obj(), conn_sp1.get_cpp_obj());
		this->get_cpp_obj()->connect(conn_);
	}

	//WRAPPED void connect(const RTLIL::SigSpec &lhs, const RTLIL::SigSpec &rhs); FROM FILE kernel/rtlil.h
	void Module::connect_SigSpec_SigSpec(SigSpec *lhs, SigSpec *rhs)
	{
		this->get_cpp_obj()->connect(*lhs->get_cpp_obj(), *rhs->get_cpp_obj());
	}

	//WRAPPED void new_connections(const std::vector<RTLIL::SigSig> &new_conn); FROM FILE kernel/rtlil.h
	void Module::new_connections(boost::python::list new_conn)
	{
		std::vector<Yosys::RTLIL::SigSig> new_conn_;
		while(len(new_conn) > 0)
		{
			boost::python::tuple tmp1 = boost::python::extract<boost::python::tuple>(new_conn.pop());
			SigSpec tmp2 = boost::python::extract<SigSpec>(tmp1[0]);
			SigSpec tmp3 = boost::python::extract<SigSpec>(tmp1[1]);
			new_conn_.push_back(Yosys::RTLIL::SigSig(*tmp2.get_cpp_obj(), *tmp3.get_cpp_obj()));
		}
		this->get_cpp_obj()->new_connections(new_conn_);
	}

	//WRAPPED void cloneInto(RTLIL::Module *new_mod) const; FROM FILE kernel/rtlil.h
	void Module::cloneInto(Module *new_mod)
	{
		this->get_cpp_obj()->cloneInto(new_mod->get_cpp_obj());
	}

	//WRAPPED bool has_memories() const; FROM FILE kernel/rtlil.h
	bool Module::has_memories()
	{
		return this->get_cpp_obj()->has_memories();
	}

	//WRAPPED bool has_processes() const; FROM FILE kernel/rtlil.h
	bool Module::has_processes()
	{
		return this->get_cpp_obj()->has_processes();
	}

	//WRAPPED bool has_memories_warn() const; FROM FILE kernel/rtlil.h
	bool Module::has_memories_warn()
	{
		return this->get_cpp_obj()->has_memories_warn();
	}

	//WRAPPED bool has_processes_warn() const; FROM FILE kernel/rtlil.h
	bool Module::has_processes_warn()
	{
		return this->get_cpp_obj()->has_processes_warn();
	}

	//WRAPPED RTLIL::Wire* wire(RTLIL::IdString id) { return wires_.count(id) ? wires_.at(id) : nullptr; } FROM FILE kernel/rtlil.h
	Wire Module::wire(IdString *id)
	{
		return Wire(this->get_cpp_obj()->wire(*id->get_cpp_obj()));
	}

	//WRAPPED RTLIL::Cell* cell(RTLIL::IdString id) { return cells_.count(id) ? cells_.at(id) : nullptr; } FROM FILE kernel/rtlil.h
	Cell Module::cell(IdString *id)
	{
		return Cell(this->get_cpp_obj()->cell(*id->get_cpp_obj()));
	}

	//WRAPPED void remove(const pool<RTLIL::Wire*> &wires); FROM FILE kernel/rtlil.h
	void Module::remove_pool_Wire(boost::python::list wires)
	{
		pool<Yosys::RTLIL::Wire*> wires_;
		while(len(wires) > 0)
		{
			Wire tmp = boost::python::extract<Wire>(wires.pop());
			wires_.insert(tmp.get_cpp_obj());
		}
		this->get_cpp_obj()->remove(wires_);
	}

	//WRAPPED void remove(RTLIL::Cell *cell); FROM FILE kernel/rtlil.h
	void Module::remove_Cell(Cell *cell)
	{
		this->get_cpp_obj()->remove(cell->get_cpp_obj());
	}

	//WRAPPED void rename(RTLIL::Wire *wire, RTLIL::IdString new_name); FROM FILE kernel/rtlil.h
	void Module::rename_Wire_IdString(Wire *wire, IdString *new_name)
	{
		this->get_cpp_obj()->rename(wire->get_cpp_obj(), *new_name->get_cpp_obj());
	}

	//WRAPPED void rename(RTLIL::Cell *cell, RTLIL::IdString new_name); FROM FILE kernel/rtlil.h
	void Module::rename_Cell_IdString(Cell *cell, IdString *new_name)
	{
		this->get_cpp_obj()->rename(cell->get_cpp_obj(), *new_name->get_cpp_obj());
	}

	//WRAPPED void rename(RTLIL::IdString old_name, RTLIL::IdString new_name); FROM FILE kernel/rtlil.h
	void Module::rename_IdString_IdString(IdString *old_name, IdString *new_name)
	{
		this->get_cpp_obj()->rename(*old_name->get_cpp_obj(), *new_name->get_cpp_obj());
	}

	//WRAPPED void swap_names(RTLIL::Wire *w1, RTLIL::Wire *w2); FROM FILE kernel/rtlil.h
	void Module::swap_names_Wire_Wire(Wire *w1, Wire *w2)
	{
		this->get_cpp_obj()->swap_names(w1->get_cpp_obj(), w2->get_cpp_obj());
	}

	//WRAPPED void swap_names(RTLIL::Cell *c1, RTLIL::Cell *c2); FROM FILE kernel/rtlil.h
	void Module::swap_names_Cell_Cell(Cell *c1, Cell *c2)
	{
		this->get_cpp_obj()->swap_names(c1->get_cpp_obj(), c2->get_cpp_obj());
	}

	//WRAPPED RTLIL::IdString uniquify(RTLIL::IdString name); FROM FILE kernel/rtlil.h
	IdString Module::uniquify_IdString(IdString *name)
	{
		return IdString(this->get_cpp_obj()->uniquify(*name->get_cpp_obj()));
	}

	//WRAPPED RTLIL::IdString uniquify(RTLIL::IdString name, int &index); FROM FILE kernel/rtlil.h
	IdString Module::uniquify_IdString_int(IdString *name, int index)
	{
		return IdString(this->get_cpp_obj()->uniquify(*name->get_cpp_obj(), index));
	}

	//WRAPPED RTLIL::Wire *addWire(RTLIL::IdString name, int width = 1); FROM FILE kernel/rtlil.h
	Wire Module::addWire_IdString_int(IdString *name, int width)
	{
		return Wire(this->get_cpp_obj()->addWire(*name->get_cpp_obj(), width));
	}

	//WRAPPED RTLIL::Wire *addWire(RTLIL::IdString name, const RTLIL::Wire *other); FROM FILE kernel/rtlil.h
	Wire Module::addWire_IdString_Wire(IdString *name, Wire *other)
	{
		return Wire(this->get_cpp_obj()->addWire(*name->get_cpp_obj(), other->get_cpp_obj()));
	}

	//WRAPPED RTLIL::Cell *addCell(RTLIL::IdString name, RTLIL::IdString type); FROM FILE kernel/rtlil.h
	Cell Module::addCell_IdString_IdString(IdString *name, IdString *type)
	{
		return Cell(this->get_cpp_obj()->addCell(*name->get_cpp_obj(), *type->get_cpp_obj()));
	}

	//WRAPPED RTLIL::Cell *addCell(RTLIL::IdString name, const RTLIL::Cell *other); FROM FILE kernel/rtlil.h
	Cell Module::addCell_IdString_Cell(IdString *name, Cell *other)
	{
		return Cell(this->get_cpp_obj()->addCell(*name->get_cpp_obj(), other->get_cpp_obj()));
	}

	//WRAPPED RTLIL::Cell* addNot(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addNot(IdString *name, SigSpec *sig_a, SigSpec *sig_y, bool is_signed, std::string src)
	{
		return Cell(this->get_cpp_obj()->addNot(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_y->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::Cell* addPos(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addPos(IdString *name, SigSpec *sig_a, SigSpec *sig_y, bool is_signed, std::string src)
	{
		return Cell(this->get_cpp_obj()->addPos(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_y->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::Cell* addNeg(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addNeg(IdString *name, SigSpec *sig_a, SigSpec *sig_y, bool is_signed, std::string src)
	{
		return Cell(this->get_cpp_obj()->addNeg(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_y->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::Cell* addAnd(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addAnd(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed, std::string src)
	{
		return Cell(this->get_cpp_obj()->addAnd(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_y->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::Cell* addOr(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addOr(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed, std::string src)
	{
		return Cell(this->get_cpp_obj()->addOr(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_y->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::Cell* addXor(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addXor(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed, std::string src)
	{
		return Cell(this->get_cpp_obj()->addXor(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_y->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::Cell* addXnor(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addXnor(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed, std::string src)
	{
		return Cell(this->get_cpp_obj()->addXnor(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_y->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::Cell* addReduceAnd(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addReduceAnd(IdString *name, SigSpec *sig_a, SigSpec *sig_y, bool is_signed, std::string src)
	{
		return Cell(this->get_cpp_obj()->addReduceAnd(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_y->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::Cell* addReduceOr(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addReduceOr(IdString *name, SigSpec *sig_a, SigSpec *sig_y, bool is_signed, std::string src)
	{
		return Cell(this->get_cpp_obj()->addReduceOr(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_y->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::Cell* addReduceXor(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addReduceXor(IdString *name, SigSpec *sig_a, SigSpec *sig_y, bool is_signed, std::string src)
	{
		return Cell(this->get_cpp_obj()->addReduceXor(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_y->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::Cell* addReduceXnor(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addReduceXnor(IdString *name, SigSpec *sig_a, SigSpec *sig_y, bool is_signed, std::string src)
	{
		return Cell(this->get_cpp_obj()->addReduceXnor(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_y->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::Cell* addReduceBool(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addReduceBool(IdString *name, SigSpec *sig_a, SigSpec *sig_y, bool is_signed, std::string src)
	{
		return Cell(this->get_cpp_obj()->addReduceBool(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_y->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::Cell* addShl(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addShl(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed, std::string src)
	{
		return Cell(this->get_cpp_obj()->addShl(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_y->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::Cell* addShr(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addShr(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed, std::string src)
	{
		return Cell(this->get_cpp_obj()->addShr(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_y->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::Cell* addSshl(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addSshl(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed, std::string src)
	{
		return Cell(this->get_cpp_obj()->addSshl(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_y->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::Cell* addSshr(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addSshr(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed, std::string src)
	{
		return Cell(this->get_cpp_obj()->addSshr(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_y->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::Cell* addShift(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addShift(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed, std::string src)
	{
		return Cell(this->get_cpp_obj()->addShift(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_y->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::Cell* addShiftx(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addShiftx(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed, std::string src)
	{
		return Cell(this->get_cpp_obj()->addShiftx(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_y->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::Cell* addLt(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addLt(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed, std::string src)
	{
		return Cell(this->get_cpp_obj()->addLt(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_y->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::Cell* addLe(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addLe(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed, std::string src)
	{
		return Cell(this->get_cpp_obj()->addLe(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_y->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::Cell* addEq(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addEq(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed, std::string src)
	{
		return Cell(this->get_cpp_obj()->addEq(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_y->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::Cell* addNe(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addNe(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed, std::string src)
	{
		return Cell(this->get_cpp_obj()->addNe(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_y->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::Cell* addEqx(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addEqx(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed, std::string src)
	{
		return Cell(this->get_cpp_obj()->addEqx(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_y->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::Cell* addNex(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addNex(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed, std::string src)
	{
		return Cell(this->get_cpp_obj()->addNex(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_y->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::Cell* addGe(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addGe(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed, std::string src)
	{
		return Cell(this->get_cpp_obj()->addGe(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_y->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::Cell* addGt(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addGt(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed, std::string src)
	{
		return Cell(this->get_cpp_obj()->addGt(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_y->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::Cell* addAdd(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addAdd(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed, std::string src)
	{
		return Cell(this->get_cpp_obj()->addAdd(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_y->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::Cell* addSub(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addSub(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed, std::string src)
	{
		return Cell(this->get_cpp_obj()->addSub(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_y->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::Cell* addMul(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addMul(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed, std::string src)
	{
		return Cell(this->get_cpp_obj()->addMul(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_y->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::Cell* addDiv(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addDiv(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed, std::string src)
	{
		return Cell(this->get_cpp_obj()->addDiv(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_y->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::Cell* addMod(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addMod(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed, std::string src)
	{
		return Cell(this->get_cpp_obj()->addMod(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_y->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::Cell* addPow(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool a_signed = false, bool b_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addPow(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool a_signed, bool b_signed, std::string src)
	{
		return Cell(this->get_cpp_obj()->addPow(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_y->get_cpp_obj(), a_signed, b_signed, src));
	}

	//WRAPPED RTLIL::Cell* addLogicNot(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addLogicNot(IdString *name, SigSpec *sig_a, SigSpec *sig_y, bool is_signed, std::string src)
	{
		return Cell(this->get_cpp_obj()->addLogicNot(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_y->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::Cell* addLogicAnd(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addLogicAnd(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed, std::string src)
	{
		return Cell(this->get_cpp_obj()->addLogicAnd(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_y->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::Cell* addLogicOr(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addLogicOr(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, bool is_signed, std::string src)
	{
		return Cell(this->get_cpp_obj()->addLogicOr(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_y->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::Cell* addMux(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_s, RTLIL::SigSpec sig_y, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addMux(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_s, SigSpec *sig_y, std::string src)
	{
		return Cell(this->get_cpp_obj()->addMux(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_s->get_cpp_obj(), *sig_y->get_cpp_obj(), src));
	}

	//WRAPPED RTLIL::Cell* addPmux(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_s, RTLIL::SigSpec sig_y, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addPmux(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_s, SigSpec *sig_y, std::string src)
	{
		return Cell(this->get_cpp_obj()->addPmux(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_s->get_cpp_obj(), *sig_y->get_cpp_obj(), src));
	}

	//WRAPPED RTLIL::Cell* addSlice(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_y, RTLIL::Const offset, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addSlice(IdString *name, SigSpec *sig_a, SigSpec *sig_y, Const *offset, std::string src)
	{
		return Cell(this->get_cpp_obj()->addSlice(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_y->get_cpp_obj(), *offset->get_cpp_obj(), src));
	}

	//WRAPPED RTLIL::Cell* addConcat(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addConcat(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, std::string src)
	{
		return Cell(this->get_cpp_obj()->addConcat(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_y->get_cpp_obj(), src));
	}

	//WRAPPED RTLIL::Cell* addLut(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_y, RTLIL::Const lut, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addLut(IdString *name, SigSpec *sig_a, SigSpec *sig_y, Const *lut, std::string src)
	{
		return Cell(this->get_cpp_obj()->addLut(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_y->get_cpp_obj(), *lut->get_cpp_obj(), src));
	}

	//WRAPPED RTLIL::Cell* addTribuf(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_en, RTLIL::SigSpec sig_y, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addTribuf(IdString *name, SigSpec *sig_a, SigSpec *sig_en, SigSpec *sig_y, std::string src)
	{
		return Cell(this->get_cpp_obj()->addTribuf(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_en->get_cpp_obj(), *sig_y->get_cpp_obj(), src));
	}

	//WRAPPED RTLIL::Cell* addAssert(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_en, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addAssert(IdString *name, SigSpec *sig_a, SigSpec *sig_en, std::string src)
	{
		return Cell(this->get_cpp_obj()->addAssert(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_en->get_cpp_obj(), src));
	}

	//WRAPPED RTLIL::Cell* addAssume(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_en, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addAssume(IdString *name, SigSpec *sig_a, SigSpec *sig_en, std::string src)
	{
		return Cell(this->get_cpp_obj()->addAssume(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_en->get_cpp_obj(), src));
	}

	//WRAPPED RTLIL::Cell* addLive(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_en, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addLive(IdString *name, SigSpec *sig_a, SigSpec *sig_en, std::string src)
	{
		return Cell(this->get_cpp_obj()->addLive(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_en->get_cpp_obj(), src));
	}

	//WRAPPED RTLIL::Cell* addFair(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_en, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addFair(IdString *name, SigSpec *sig_a, SigSpec *sig_en, std::string src)
	{
		return Cell(this->get_cpp_obj()->addFair(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_en->get_cpp_obj(), src));
	}

	//WRAPPED RTLIL::Cell* addCover(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_en, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addCover(IdString *name, SigSpec *sig_a, SigSpec *sig_en, std::string src)
	{
		return Cell(this->get_cpp_obj()->addCover(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_en->get_cpp_obj(), src));
	}

	//WRAPPED RTLIL::Cell* addEquiv(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addEquiv(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_y, std::string src)
	{
		return Cell(this->get_cpp_obj()->addEquiv(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_y->get_cpp_obj(), src));
	}

	//WRAPPED RTLIL::Cell* addSr(RTLIL::IdString name, RTLIL::SigSpec sig_set, RTLIL::SigSpec sig_clr, RTLIL::SigSpec sig_q, bool set_polarity = true, bool clr_polarity = true, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addSr(IdString *name, SigSpec *sig_set, SigSpec *sig_clr, SigSpec *sig_q, bool set_polarity, bool clr_polarity, std::string src)
	{
		return Cell(this->get_cpp_obj()->addSr(*name->get_cpp_obj(), *sig_set->get_cpp_obj(), *sig_clr->get_cpp_obj(), *sig_q->get_cpp_obj(), set_polarity, clr_polarity, src));
	}

	//WRAPPED RTLIL::Cell* addFf(RTLIL::IdString name, RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addFf(IdString *name, SigSpec *sig_d, SigSpec *sig_q, std::string src)
	{
		return Cell(this->get_cpp_obj()->addFf(*name->get_cpp_obj(), *sig_d->get_cpp_obj(), *sig_q->get_cpp_obj(), src));
	}

	//WRAPPED RTLIL::Cell* addDff(RTLIL::IdString name, RTLIL::SigSpec sig_clk, RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool clk_polarity = true, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addDff(IdString *name, SigSpec *sig_clk, SigSpec *sig_d, SigSpec *sig_q, bool clk_polarity, std::string src)
	{
		return Cell(this->get_cpp_obj()->addDff(*name->get_cpp_obj(), *sig_clk->get_cpp_obj(), *sig_d->get_cpp_obj(), *sig_q->get_cpp_obj(), clk_polarity, src));
	}

	//WRAPPED RTLIL::Cell* addDffe(RTLIL::IdString name, RTLIL::SigSpec sig_clk, RTLIL::SigSpec sig_en, RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool clk_polarity = true, bool en_polarity = true, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addDffe(IdString *name, SigSpec *sig_clk, SigSpec *sig_en, SigSpec *sig_d, SigSpec *sig_q, bool clk_polarity, bool en_polarity, std::string src)
	{
		return Cell(this->get_cpp_obj()->addDffe(*name->get_cpp_obj(), *sig_clk->get_cpp_obj(), *sig_en->get_cpp_obj(), *sig_d->get_cpp_obj(), *sig_q->get_cpp_obj(), clk_polarity, en_polarity, src));
	}

	//WRAPPED RTLIL::Cell* addDffsr(RTLIL::IdString name, RTLIL::SigSpec sig_clk, RTLIL::SigSpec sig_set, RTLIL::SigSpec sig_clr,RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool clk_polarity = true, bool set_polarity = true, bool clr_polarity = true, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addDffsr(IdString *name, SigSpec *sig_clk, SigSpec *sig_set, SigSpec *sig_clr, SigSpec *sig_d, SigSpec *sig_q, bool clk_polarity, bool set_polarity, bool clr_polarity, std::string src)
	{
		return Cell(this->get_cpp_obj()->addDffsr(*name->get_cpp_obj(), *sig_clk->get_cpp_obj(), *sig_set->get_cpp_obj(), *sig_clr->get_cpp_obj(), *sig_d->get_cpp_obj(), *sig_q->get_cpp_obj(), clk_polarity, set_polarity, clr_polarity, src));
	}

	//WRAPPED RTLIL::Cell* addAdff(RTLIL::IdString name, RTLIL::SigSpec sig_clk, RTLIL::SigSpec sig_arst, RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q,RTLIL::Const arst_value, bool clk_polarity = true, bool arst_polarity = true, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addAdff(IdString *name, SigSpec *sig_clk, SigSpec *sig_arst, SigSpec *sig_d, SigSpec *sig_q, Const *arst_value, bool clk_polarity, bool arst_polarity, std::string src)
	{
		return Cell(this->get_cpp_obj()->addAdff(*name->get_cpp_obj(), *sig_clk->get_cpp_obj(), *sig_arst->get_cpp_obj(), *sig_d->get_cpp_obj(), *sig_q->get_cpp_obj(), *arst_value->get_cpp_obj(), clk_polarity, arst_polarity, src));
	}

	//WRAPPED RTLIL::Cell* addDlatch(RTLIL::IdString name, RTLIL::SigSpec sig_en, RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool en_polarity = true, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addDlatch(IdString *name, SigSpec *sig_en, SigSpec *sig_d, SigSpec *sig_q, bool en_polarity, std::string src)
	{
		return Cell(this->get_cpp_obj()->addDlatch(*name->get_cpp_obj(), *sig_en->get_cpp_obj(), *sig_d->get_cpp_obj(), *sig_q->get_cpp_obj(), en_polarity, src));
	}

	//WRAPPED RTLIL::Cell* addDlatchsr(RTLIL::IdString name, RTLIL::SigSpec sig_en, RTLIL::SigSpec sig_set, RTLIL::SigSpec sig_clr,RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool en_polarity = true, bool set_polarity = true, bool clr_polarity = true, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addDlatchsr(IdString *name, SigSpec *sig_en, SigSpec *sig_set, SigSpec *sig_clr, SigSpec *sig_d, SigSpec *sig_q, bool en_polarity, bool set_polarity, bool clr_polarity, std::string src)
	{
		return Cell(this->get_cpp_obj()->addDlatchsr(*name->get_cpp_obj(), *sig_en->get_cpp_obj(), *sig_set->get_cpp_obj(), *sig_clr->get_cpp_obj(), *sig_d->get_cpp_obj(), *sig_q->get_cpp_obj(), en_polarity, set_polarity, clr_polarity, src));
	}

	//WRAPPED RTLIL::Cell* addBufGate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_y, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addBufGate(IdString *name, SigBit *sig_a, SigBit *sig_y, std::string src)
	{
		return Cell(this->get_cpp_obj()->addBufGate(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_y->get_cpp_obj(), src));
	}

	//WRAPPED RTLIL::Cell* addNotGate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_y, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addNotGate(IdString *name, SigBit *sig_a, SigBit *sig_y, std::string src)
	{
		return Cell(this->get_cpp_obj()->addNotGate(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_y->get_cpp_obj(), src));
	}

	//WRAPPED RTLIL::Cell* addAndGate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, RTLIL::SigBit sig_y, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addAndGate(IdString *name, SigBit *sig_a, SigBit *sig_b, SigBit *sig_y, std::string src)
	{
		return Cell(this->get_cpp_obj()->addAndGate(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_y->get_cpp_obj(), src));
	}

	//WRAPPED RTLIL::Cell* addNandGate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, RTLIL::SigBit sig_y, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addNandGate(IdString *name, SigBit *sig_a, SigBit *sig_b, SigBit *sig_y, std::string src)
	{
		return Cell(this->get_cpp_obj()->addNandGate(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_y->get_cpp_obj(), src));
	}

	//WRAPPED RTLIL::Cell* addOrGate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, RTLIL::SigBit sig_y, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addOrGate(IdString *name, SigBit *sig_a, SigBit *sig_b, SigBit *sig_y, std::string src)
	{
		return Cell(this->get_cpp_obj()->addOrGate(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_y->get_cpp_obj(), src));
	}

	//WRAPPED RTLIL::Cell* addNorGate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, RTLIL::SigBit sig_y, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addNorGate(IdString *name, SigBit *sig_a, SigBit *sig_b, SigBit *sig_y, std::string src)
	{
		return Cell(this->get_cpp_obj()->addNorGate(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_y->get_cpp_obj(), src));
	}

	//WRAPPED RTLIL::Cell* addXorGate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, RTLIL::SigBit sig_y, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addXorGate(IdString *name, SigBit *sig_a, SigBit *sig_b, SigBit *sig_y, std::string src)
	{
		return Cell(this->get_cpp_obj()->addXorGate(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_y->get_cpp_obj(), src));
	}

	//WRAPPED RTLIL::Cell* addXnorGate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, RTLIL::SigBit sig_y, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addXnorGate(IdString *name, SigBit *sig_a, SigBit *sig_b, SigBit *sig_y, std::string src)
	{
		return Cell(this->get_cpp_obj()->addXnorGate(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_y->get_cpp_obj(), src));
	}

	//WRAPPED RTLIL::Cell* addAndnotGate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, RTLIL::SigBit sig_y, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addAndnotGate(IdString *name, SigBit *sig_a, SigBit *sig_b, SigBit *sig_y, std::string src)
	{
		return Cell(this->get_cpp_obj()->addAndnotGate(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_y->get_cpp_obj(), src));
	}

	//WRAPPED RTLIL::Cell* addOrnotGate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, RTLIL::SigBit sig_y, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addOrnotGate(IdString *name, SigBit *sig_a, SigBit *sig_b, SigBit *sig_y, std::string src)
	{
		return Cell(this->get_cpp_obj()->addOrnotGate(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_y->get_cpp_obj(), src));
	}

	//WRAPPED RTLIL::Cell* addMuxGate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, RTLIL::SigBit sig_s, RTLIL::SigBit sig_y, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addMuxGate(IdString *name, SigBit *sig_a, SigBit *sig_b, SigBit *sig_s, SigBit *sig_y, std::string src)
	{
		return Cell(this->get_cpp_obj()->addMuxGate(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_s->get_cpp_obj(), *sig_y->get_cpp_obj(), src));
	}

	//WRAPPED RTLIL::Cell* addAoi3Gate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, RTLIL::SigBit sig_c, RTLIL::SigBit sig_y, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addAoi3Gate(IdString *name, SigBit *sig_a, SigBit *sig_b, SigBit *sig_c, SigBit *sig_y, std::string src)
	{
		return Cell(this->get_cpp_obj()->addAoi3Gate(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_c->get_cpp_obj(), *sig_y->get_cpp_obj(), src));
	}

	//WRAPPED RTLIL::Cell* addOai3Gate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, RTLIL::SigBit sig_c, RTLIL::SigBit sig_y, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addOai3Gate(IdString *name, SigBit *sig_a, SigBit *sig_b, SigBit *sig_c, SigBit *sig_y, std::string src)
	{
		return Cell(this->get_cpp_obj()->addOai3Gate(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_c->get_cpp_obj(), *sig_y->get_cpp_obj(), src));
	}

	//WRAPPED RTLIL::Cell* addAoi4Gate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, RTLIL::SigBit sig_c, RTLIL::SigBit sig_d, RTLIL::SigBit sig_y, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addAoi4Gate(IdString *name, SigBit *sig_a, SigBit *sig_b, SigBit *sig_c, SigBit *sig_d, SigBit *sig_y, std::string src)
	{
		return Cell(this->get_cpp_obj()->addAoi4Gate(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_c->get_cpp_obj(), *sig_d->get_cpp_obj(), *sig_y->get_cpp_obj(), src));
	}

	//WRAPPED RTLIL::Cell* addOai4Gate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, RTLIL::SigBit sig_c, RTLIL::SigBit sig_d, RTLIL::SigBit sig_y, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addOai4Gate(IdString *name, SigBit *sig_a, SigBit *sig_b, SigBit *sig_c, SigBit *sig_d, SigBit *sig_y, std::string src)
	{
		return Cell(this->get_cpp_obj()->addOai4Gate(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_c->get_cpp_obj(), *sig_d->get_cpp_obj(), *sig_y->get_cpp_obj(), src));
	}

	//WRAPPED RTLIL::Cell* addFfGate(RTLIL::IdString name, RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addFfGate(IdString *name, SigSpec *sig_d, SigSpec *sig_q, std::string src)
	{
		return Cell(this->get_cpp_obj()->addFfGate(*name->get_cpp_obj(), *sig_d->get_cpp_obj(), *sig_q->get_cpp_obj(), src));
	}

	//WRAPPED RTLIL::Cell* addDffGate(RTLIL::IdString name, RTLIL::SigSpec sig_clk, RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool clk_polarity = true, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addDffGate(IdString *name, SigSpec *sig_clk, SigSpec *sig_d, SigSpec *sig_q, bool clk_polarity, std::string src)
	{
		return Cell(this->get_cpp_obj()->addDffGate(*name->get_cpp_obj(), *sig_clk->get_cpp_obj(), *sig_d->get_cpp_obj(), *sig_q->get_cpp_obj(), clk_polarity, src));
	}

	//WRAPPED RTLIL::Cell* addDffeGate(RTLIL::IdString name, RTLIL::SigSpec sig_clk, RTLIL::SigSpec sig_en, RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool clk_polarity = true, bool en_polarity = true, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addDffeGate(IdString *name, SigSpec *sig_clk, SigSpec *sig_en, SigSpec *sig_d, SigSpec *sig_q, bool clk_polarity, bool en_polarity, std::string src)
	{
		return Cell(this->get_cpp_obj()->addDffeGate(*name->get_cpp_obj(), *sig_clk->get_cpp_obj(), *sig_en->get_cpp_obj(), *sig_d->get_cpp_obj(), *sig_q->get_cpp_obj(), clk_polarity, en_polarity, src));
	}

	//WRAPPED RTLIL::Cell* addDffsrGate(RTLIL::IdString name, RTLIL::SigSpec sig_clk, RTLIL::SigSpec sig_set, RTLIL::SigSpec sig_clr,RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool clk_polarity = true, bool set_polarity = true, bool clr_polarity = true, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addDffsrGate(IdString *name, SigSpec *sig_clk, SigSpec *sig_set, SigSpec *sig_clr, SigSpec *sig_d, SigSpec *sig_q, bool clk_polarity, bool set_polarity, bool clr_polarity, std::string src)
	{
		return Cell(this->get_cpp_obj()->addDffsrGate(*name->get_cpp_obj(), *sig_clk->get_cpp_obj(), *sig_set->get_cpp_obj(), *sig_clr->get_cpp_obj(), *sig_d->get_cpp_obj(), *sig_q->get_cpp_obj(), clk_polarity, set_polarity, clr_polarity, src));
	}

	//WRAPPED RTLIL::Cell* addAdffGate(RTLIL::IdString name, RTLIL::SigSpec sig_clk, RTLIL::SigSpec sig_arst, RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q,bool arst_value = false, bool clk_polarity = true, bool arst_polarity = true, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addAdffGate(IdString *name, SigSpec *sig_clk, SigSpec *sig_arst, SigSpec *sig_d, SigSpec *sig_q, bool arst_value, bool clk_polarity, bool arst_polarity, std::string src)
	{
		return Cell(this->get_cpp_obj()->addAdffGate(*name->get_cpp_obj(), *sig_clk->get_cpp_obj(), *sig_arst->get_cpp_obj(), *sig_d->get_cpp_obj(), *sig_q->get_cpp_obj(), arst_value, clk_polarity, arst_polarity, src));
	}

	//WRAPPED RTLIL::Cell* addDlatchGate(RTLIL::IdString name, RTLIL::SigSpec sig_en, RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool en_polarity = true, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addDlatchGate(IdString *name, SigSpec *sig_en, SigSpec *sig_d, SigSpec *sig_q, bool en_polarity, std::string src)
	{
		return Cell(this->get_cpp_obj()->addDlatchGate(*name->get_cpp_obj(), *sig_en->get_cpp_obj(), *sig_d->get_cpp_obj(), *sig_q->get_cpp_obj(), en_polarity, src));
	}

	//WRAPPED RTLIL::Cell* addDlatchsrGate(RTLIL::IdString name, RTLIL::SigSpec sig_en, RTLIL::SigSpec sig_set, RTLIL::SigSpec sig_clr,RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool en_polarity = true, bool set_polarity = true, bool clr_polarity = true, const std::string &src = ""); FROM FILE kernel/rtlil.h
	Cell Module::addDlatchsrGate(IdString *name, SigSpec *sig_en, SigSpec *sig_set, SigSpec *sig_clr, SigSpec *sig_d, SigSpec *sig_q, bool en_polarity, bool set_polarity, bool clr_polarity, std::string src)
	{
		return Cell(this->get_cpp_obj()->addDlatchsrGate(*name->get_cpp_obj(), *sig_en->get_cpp_obj(), *sig_set->get_cpp_obj(), *sig_clr->get_cpp_obj(), *sig_d->get_cpp_obj(), *sig_q->get_cpp_obj(), en_polarity, set_polarity, clr_polarity, src));
	}

	//WRAPPED RTLIL::SigSpec Not(RTLIL::IdString name, RTLIL::SigSpec sig_a, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigSpec Module::Not(IdString *name, SigSpec *sig_a, bool is_signed, std::string src)
	{
		return SigSpec(this->get_cpp_obj()->Not(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::SigSpec Pos(RTLIL::IdString name, RTLIL::SigSpec sig_a, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigSpec Module::Pos(IdString *name, SigSpec *sig_a, bool is_signed, std::string src)
	{
		return SigSpec(this->get_cpp_obj()->Pos(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::SigSpec Neg(RTLIL::IdString name, RTLIL::SigSpec sig_a, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigSpec Module::Neg(IdString *name, SigSpec *sig_a, bool is_signed, std::string src)
	{
		return SigSpec(this->get_cpp_obj()->Neg(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::SigSpec And(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigSpec Module::And(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed, std::string src)
	{
		return SigSpec(this->get_cpp_obj()->And(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::SigSpec Or(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigSpec Module::Or(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed, std::string src)
	{
		return SigSpec(this->get_cpp_obj()->Or(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::SigSpec Xor(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigSpec Module::Xor(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed, std::string src)
	{
		return SigSpec(this->get_cpp_obj()->Xor(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::SigSpec Xnor(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigSpec Module::Xnor(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed, std::string src)
	{
		return SigSpec(this->get_cpp_obj()->Xnor(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::SigSpec ReduceAnd(RTLIL::IdString name, RTLIL::SigSpec sig_a, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigSpec Module::ReduceAnd(IdString *name, SigSpec *sig_a, bool is_signed, std::string src)
	{
		return SigSpec(this->get_cpp_obj()->ReduceAnd(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::SigSpec ReduceOr(RTLIL::IdString name, RTLIL::SigSpec sig_a, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigSpec Module::ReduceOr(IdString *name, SigSpec *sig_a, bool is_signed, std::string src)
	{
		return SigSpec(this->get_cpp_obj()->ReduceOr(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::SigSpec ReduceXor(RTLIL::IdString name, RTLIL::SigSpec sig_a, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigSpec Module::ReduceXor(IdString *name, SigSpec *sig_a, bool is_signed, std::string src)
	{
		return SigSpec(this->get_cpp_obj()->ReduceXor(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::SigSpec ReduceXnor(RTLIL::IdString name, RTLIL::SigSpec sig_a, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigSpec Module::ReduceXnor(IdString *name, SigSpec *sig_a, bool is_signed, std::string src)
	{
		return SigSpec(this->get_cpp_obj()->ReduceXnor(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::SigSpec ReduceBool(RTLIL::IdString name, RTLIL::SigSpec sig_a, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigSpec Module::ReduceBool(IdString *name, SigSpec *sig_a, bool is_signed, std::string src)
	{
		return SigSpec(this->get_cpp_obj()->ReduceBool(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::SigSpec Shl(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigSpec Module::Shl(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed, std::string src)
	{
		return SigSpec(this->get_cpp_obj()->Shl(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::SigSpec Shr(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigSpec Module::Shr(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed, std::string src)
	{
		return SigSpec(this->get_cpp_obj()->Shr(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::SigSpec Sshl(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigSpec Module::Sshl(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed, std::string src)
	{
		return SigSpec(this->get_cpp_obj()->Sshl(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::SigSpec Sshr(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigSpec Module::Sshr(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed, std::string src)
	{
		return SigSpec(this->get_cpp_obj()->Sshr(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::SigSpec Shift(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigSpec Module::Shift(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed, std::string src)
	{
		return SigSpec(this->get_cpp_obj()->Shift(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::SigSpec Shiftx(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigSpec Module::Shiftx(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed, std::string src)
	{
		return SigSpec(this->get_cpp_obj()->Shiftx(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::SigSpec Lt(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigSpec Module::Lt(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed, std::string src)
	{
		return SigSpec(this->get_cpp_obj()->Lt(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::SigSpec Le(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigSpec Module::Le(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed, std::string src)
	{
		return SigSpec(this->get_cpp_obj()->Le(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::SigSpec Eq(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigSpec Module::Eq(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed, std::string src)
	{
		return SigSpec(this->get_cpp_obj()->Eq(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::SigSpec Ne(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigSpec Module::Ne(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed, std::string src)
	{
		return SigSpec(this->get_cpp_obj()->Ne(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::SigSpec Eqx(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigSpec Module::Eqx(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed, std::string src)
	{
		return SigSpec(this->get_cpp_obj()->Eqx(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::SigSpec Nex(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigSpec Module::Nex(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed, std::string src)
	{
		return SigSpec(this->get_cpp_obj()->Nex(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::SigSpec Ge(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigSpec Module::Ge(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed, std::string src)
	{
		return SigSpec(this->get_cpp_obj()->Ge(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::SigSpec Gt(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigSpec Module::Gt(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed, std::string src)
	{
		return SigSpec(this->get_cpp_obj()->Gt(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::SigSpec Add(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigSpec Module::Add(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed, std::string src)
	{
		return SigSpec(this->get_cpp_obj()->Add(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::SigSpec Sub(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigSpec Module::Sub(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed, std::string src)
	{
		return SigSpec(this->get_cpp_obj()->Sub(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::SigSpec Mul(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigSpec Module::Mul(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed, std::string src)
	{
		return SigSpec(this->get_cpp_obj()->Mul(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::SigSpec Div(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigSpec Module::Div(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed, std::string src)
	{
		return SigSpec(this->get_cpp_obj()->Div(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::SigSpec Mod(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigSpec Module::Mod(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed, std::string src)
	{
		return SigSpec(this->get_cpp_obj()->Mod(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::SigSpec LogicNot(RTLIL::IdString name, RTLIL::SigSpec sig_a, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigSpec Module::LogicNot(IdString *name, SigSpec *sig_a, bool is_signed, std::string src)
	{
		return SigSpec(this->get_cpp_obj()->LogicNot(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::SigSpec LogicAnd(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigSpec Module::LogicAnd(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed, std::string src)
	{
		return SigSpec(this->get_cpp_obj()->LogicAnd(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::SigSpec LogicOr(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigSpec Module::LogicOr(IdString *name, SigSpec *sig_a, SigSpec *sig_b, bool is_signed, std::string src)
	{
		return SigSpec(this->get_cpp_obj()->LogicOr(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), is_signed, src));
	}

	//WRAPPED RTLIL::SigSpec Mux(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_s, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigSpec Module::Mux(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_s, std::string src)
	{
		return SigSpec(this->get_cpp_obj()->Mux(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_s->get_cpp_obj(), src));
	}

	//WRAPPED RTLIL::SigSpec Pmux(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_s, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigSpec Module::Pmux(IdString *name, SigSpec *sig_a, SigSpec *sig_b, SigSpec *sig_s, std::string src)
	{
		return SigSpec(this->get_cpp_obj()->Pmux(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_s->get_cpp_obj(), src));
	}

	//WRAPPED RTLIL::SigBit BufGate(RTLIL::IdString name, RTLIL::SigBit sig_a, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigBit Module::BufGate(IdString *name, SigBit *sig_a, std::string src)
	{
		return SigBit(this->get_cpp_obj()->BufGate(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), src));
	}

	//WRAPPED RTLIL::SigBit NotGate(RTLIL::IdString name, RTLIL::SigBit sig_a, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigBit Module::NotGate(IdString *name, SigBit *sig_a, std::string src)
	{
		return SigBit(this->get_cpp_obj()->NotGate(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), src));
	}

	//WRAPPED RTLIL::SigBit AndGate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigBit Module::AndGate(IdString *name, SigBit *sig_a, SigBit *sig_b, std::string src)
	{
		return SigBit(this->get_cpp_obj()->AndGate(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), src));
	}

	//WRAPPED RTLIL::SigBit NandGate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigBit Module::NandGate(IdString *name, SigBit *sig_a, SigBit *sig_b, std::string src)
	{
		return SigBit(this->get_cpp_obj()->NandGate(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), src));
	}

	//WRAPPED RTLIL::SigBit OrGate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigBit Module::OrGate(IdString *name, SigBit *sig_a, SigBit *sig_b, std::string src)
	{
		return SigBit(this->get_cpp_obj()->OrGate(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), src));
	}

	//WRAPPED RTLIL::SigBit NorGate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigBit Module::NorGate(IdString *name, SigBit *sig_a, SigBit *sig_b, std::string src)
	{
		return SigBit(this->get_cpp_obj()->NorGate(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), src));
	}

	//WRAPPED RTLIL::SigBit XorGate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigBit Module::XorGate(IdString *name, SigBit *sig_a, SigBit *sig_b, std::string src)
	{
		return SigBit(this->get_cpp_obj()->XorGate(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), src));
	}

	//WRAPPED RTLIL::SigBit XnorGate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigBit Module::XnorGate(IdString *name, SigBit *sig_a, SigBit *sig_b, std::string src)
	{
		return SigBit(this->get_cpp_obj()->XnorGate(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), src));
	}

	//WRAPPED RTLIL::SigBit AndnotGate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigBit Module::AndnotGate(IdString *name, SigBit *sig_a, SigBit *sig_b, std::string src)
	{
		return SigBit(this->get_cpp_obj()->AndnotGate(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), src));
	}

	//WRAPPED RTLIL::SigBit OrnotGate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigBit Module::OrnotGate(IdString *name, SigBit *sig_a, SigBit *sig_b, std::string src)
	{
		return SigBit(this->get_cpp_obj()->OrnotGate(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), src));
	}

	//WRAPPED RTLIL::SigBit MuxGate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, RTLIL::SigBit sig_s, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigBit Module::MuxGate(IdString *name, SigBit *sig_a, SigBit *sig_b, SigBit *sig_s, std::string src)
	{
		return SigBit(this->get_cpp_obj()->MuxGate(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_s->get_cpp_obj(), src));
	}

	//WRAPPED RTLIL::SigBit Aoi3Gate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, RTLIL::SigBit sig_c, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigBit Module::Aoi3Gate(IdString *name, SigBit *sig_a, SigBit *sig_b, SigBit *sig_c, std::string src)
	{
		return SigBit(this->get_cpp_obj()->Aoi3Gate(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_c->get_cpp_obj(), src));
	}

	//WRAPPED RTLIL::SigBit Oai3Gate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, RTLIL::SigBit sig_c, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigBit Module::Oai3Gate(IdString *name, SigBit *sig_a, SigBit *sig_b, SigBit *sig_c, std::string src)
	{
		return SigBit(this->get_cpp_obj()->Oai3Gate(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_c->get_cpp_obj(), src));
	}

	//WRAPPED RTLIL::SigBit Aoi4Gate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, RTLIL::SigBit sig_c, RTLIL::SigBit sig_d, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigBit Module::Aoi4Gate(IdString *name, SigBit *sig_a, SigBit *sig_b, SigBit *sig_c, SigBit *sig_d, std::string src)
	{
		return SigBit(this->get_cpp_obj()->Aoi4Gate(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_c->get_cpp_obj(), *sig_d->get_cpp_obj(), src));
	}

	//WRAPPED RTLIL::SigBit Oai4Gate(RTLIL::IdString name, RTLIL::SigBit sig_a, RTLIL::SigBit sig_b, RTLIL::SigBit sig_c, RTLIL::SigBit sig_d, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigBit Module::Oai4Gate(IdString *name, SigBit *sig_a, SigBit *sig_b, SigBit *sig_c, SigBit *sig_d, std::string src)
	{
		return SigBit(this->get_cpp_obj()->Oai4Gate(*name->get_cpp_obj(), *sig_a->get_cpp_obj(), *sig_b->get_cpp_obj(), *sig_c->get_cpp_obj(), *sig_d->get_cpp_obj(), src));
	}

	//WRAPPED RTLIL::SigSpec Anyconst(RTLIL::IdString name, int width = 1, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigSpec Module::Anyconst(IdString *name, int width, std::string src)
	{
		return SigSpec(this->get_cpp_obj()->Anyconst(*name->get_cpp_obj(), width, src));
	}

	//WRAPPED RTLIL::SigSpec Anyseq(RTLIL::IdString name, int width = 1, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigSpec Module::Anyseq(IdString *name, int width, std::string src)
	{
		return SigSpec(this->get_cpp_obj()->Anyseq(*name->get_cpp_obj(), width, src));
	}

	//WRAPPED RTLIL::SigSpec Allconst(RTLIL::IdString name, int width = 1, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigSpec Module::Allconst(IdString *name, int width, std::string src)
	{
		return SigSpec(this->get_cpp_obj()->Allconst(*name->get_cpp_obj(), width, src));
	}

	//WRAPPED RTLIL::SigSpec Allseq(RTLIL::IdString name, int width = 1, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigSpec Module::Allseq(IdString *name, int width, std::string src)
	{
		return SigSpec(this->get_cpp_obj()->Allseq(*name->get_cpp_obj(), width, src));
	}

	//WRAPPED RTLIL::SigSpec Initstate(RTLIL::IdString name, const std::string &src = ""); FROM FILE kernel/rtlil.h
	SigSpec Module::Initstate(IdString *name, std::string src)
	{
		return SigSpec(this->get_cpp_obj()->Initstate(*name->get_cpp_obj(), src));
	}

	//WRAPPED unsigned int hash() const { return hashidx_; } FROM FILE kernel/rtlil.h
	unsigned int Design::hash()
	{
		return this->get_cpp_obj()->hash();
	}

	//WRAPPED RTLIL::Module *module(RTLIL::IdString name); FROM FILE kernel/rtlil.h
	Module Design::module(IdString *name)
	{
		return Module(this->get_cpp_obj()->module(*name->get_cpp_obj()));
	}

	//WRAPPED bool has(RTLIL::IdString id) const { FROM FILE kernel/rtlil.h
	bool Design::has(IdString *id)
	{
		return this->get_cpp_obj()->has(*id->get_cpp_obj());
	}

	//WRAPPED void add(RTLIL::Module *module); FROM FILE kernel/rtlil.h
	void Design::add(Module *module)
	{
		this->get_cpp_obj()->add(module->get_cpp_obj());
	}

	//WRAPPED RTLIL::Module *addModule(RTLIL::IdString name); FROM FILE kernel/rtlil.h
	Module Design::addModule(IdString *name)
	{
		return Module(this->get_cpp_obj()->addModule(*name->get_cpp_obj()));
	}

	//WRAPPED void remove(RTLIL::Module *module); FROM FILE kernel/rtlil.h
	void Design::remove(Module *module)
	{
		this->get_cpp_obj()->remove(module->get_cpp_obj());
	}

	//WRAPPED void rename(RTLIL::Module *module, RTLIL::IdString new_name); FROM FILE kernel/rtlil.h
	void Design::rename(Module *module, IdString *new_name)
	{
		this->get_cpp_obj()->rename(module->get_cpp_obj(), *new_name->get_cpp_obj());
	}

	//WRAPPED void scratchpad_unset(std::string varname); FROM FILE kernel/rtlil.h
	void Design::scratchpad_unset(std::string varname)
	{
		this->get_cpp_obj()->scratchpad_unset(varname);
	}

	//WRAPPED void scratchpad_set_int(std::string varname, int value); FROM FILE kernel/rtlil.h
	void Design::scratchpad_set_int(std::string varname, int value)
	{
		this->get_cpp_obj()->scratchpad_set_int(varname, value);
	}

	//WRAPPED void scratchpad_set_bool(std::string varname, bool value); FROM FILE kernel/rtlil.h
	void Design::scratchpad_set_bool(std::string varname, bool value)
	{
		this->get_cpp_obj()->scratchpad_set_bool(varname, value);
	}

	//WRAPPED void scratchpad_set_string(std::string varname, std::string value); FROM FILE kernel/rtlil.h
	void Design::scratchpad_set_string(std::string varname, std::string value)
	{
		this->get_cpp_obj()->scratchpad_set_string(varname, value);
	}

	//WRAPPED int scratchpad_get_int(std::string varname, int default_value = 0) const; FROM FILE kernel/rtlil.h
	int Design::scratchpad_get_int(std::string varname, int default_value)
	{
		return this->get_cpp_obj()->scratchpad_get_int(varname, default_value);
	}

	//WRAPPED bool scratchpad_get_bool(std::string varname, bool default_value = false) const; FROM FILE kernel/rtlil.h
	bool Design::scratchpad_get_bool(std::string varname, bool default_value)
	{
		return this->get_cpp_obj()->scratchpad_get_bool(varname, default_value);
	}

	//WRAPPED std::string scratchpad_get_string(std::string varname, std::string default_value = std::string()) const; FROM FILE kernel/rtlil.h
	std::string Design::scratchpad_get_string(std::string varname, std::string default_value)
	{
		return this->get_cpp_obj()->scratchpad_get_string(varname, default_value);
	}

	//WRAPPED bool selected_module(RTLIL::IdString mod_name) const; FROM FILE kernel/rtlil.h
	bool Design::selected_module_IdString(IdString *mod_name)
	{
		return this->get_cpp_obj()->selected_module(*mod_name->get_cpp_obj());
	}

	//WRAPPED bool selected_whole_module(RTLIL::IdString mod_name) const; FROM FILE kernel/rtlil.h
	bool Design::selected_whole_module_IdString(IdString *mod_name)
	{
		return this->get_cpp_obj()->selected_whole_module(*mod_name->get_cpp_obj());
	}

	//WRAPPED bool selected_member(RTLIL::IdString mod_name, RTLIL::IdString memb_name) const; FROM FILE kernel/rtlil.h
	bool Design::selected_member(IdString *mod_name, IdString *memb_name)
	{
		return this->get_cpp_obj()->selected_member(*mod_name->get_cpp_obj(), *memb_name->get_cpp_obj());
	}

	//WRAPPED bool selected_module(RTLIL::Module *mod) const; FROM FILE kernel/rtlil.h
	bool Design::selected_module_Module(Module *mod)
	{
		return this->get_cpp_obj()->selected_module(mod->get_cpp_obj());
	}

	//WRAPPED bool selected_whole_module(RTLIL::Module *mod) const; FROM FILE kernel/rtlil.h
	bool Design::selected_whole_module_Module(Module *mod)
	{
		return this->get_cpp_obj()->selected_whole_module(mod->get_cpp_obj());
	}

	//WRAPPED bool full_selection() const { FROM FILE kernel/rtlil.h
	bool Design::full_selection()
	{
		return this->get_cpp_obj()->full_selection();
	}

	struct Initializer
	{
		Initializer() {
			if(!Yosys::yosys_already_setup())
			{
				Yosys::log_streams.push_back(&std::cout);
				Yosys::log_error_stderr = true;
				Yosys::yosys_setup();
				Yosys::yosys_banner();
			}
		}

		Initializer(Initializer const &) {}

		~Initializer() {
			Yosys::yosys_shutdown();
		}
	};

	BOOST_PYTHON_MODULE(libyosys)
	{
		using namespace boost::python;

				enum_<Yosys::RTLIL::State>("State")
					.value("S0",Yosys::RTLIL::S0)
					.value("S1",Yosys::RTLIL::S1)
					.value("Sx",Yosys::RTLIL::Sx)
					.value("Sz",Yosys::RTLIL::Sz)
					.value("Sa",Yosys::RTLIL::Sa)
					.value("Sm",Yosys::RTLIL::Sm)
				;

				enum_<Yosys::RTLIL::SyncType>("SyncType")
					.value("ST0",Yosys::RTLIL::ST0)
					.value("ST1",Yosys::RTLIL::ST1)
					.value("STp",Yosys::RTLIL::STp)
					.value("STn",Yosys::RTLIL::STn)
					.value("STe",Yosys::RTLIL::STe)
					.value("STa",Yosys::RTLIL::STa)
					.value("STg",Yosys::RTLIL::STg)
					.value("STi",Yosys::RTLIL::STi)
				;

				enum_<Yosys::RTLIL::ConstFlags>("ConstFlags")
					.value("CONST_FLAG_NONE",Yosys::RTLIL::CONST_FLAG_NONE)
					.value("CONST_FLAG_STRING",Yosys::RTLIL::CONST_FLAG_STRING)
					.value("CONST_FLAG_SIGNED",Yosys::RTLIL::CONST_FLAG_SIGNED)
					.value("CONST_FLAG_REAL",Yosys::RTLIL::CONST_FLAG_REAL)
				;

		class_<MonitorWrap, boost::noncopyable>("Monitor")
			.def("py_notify_module_add", &Monitor::py_notify_module_add, &MonitorWrap::default_py_notify_module_add)
			.def("py_notify_module_del", &Monitor::py_notify_module_del, &MonitorWrap::default_py_notify_module_del)
			.def("py_notify_connect_cell", &Monitor::py_notify_connect_cell, &MonitorWrap::default_py_notify_connect_cell)
			.def("py_notify_connect_tuple", &Monitor::py_notify_connect_tuple, &MonitorWrap::default_py_notify_connect_tuple)
			.def("py_notify_connect_list", &Monitor::py_notify_connect_list, &MonitorWrap::default_py_notify_connect_list)
			.def("py_notify_blackout", &Monitor::py_notify_blackout, &MonitorWrap::default_py_notify_blackout)
			;

		class_<PassWrap, boost::noncopyable>("Pass", init<std::string, std::string>())
			.def("py_execute", &PyPass::py_execute, &PassWrap::default_py_execute)
			.def("py_help", &PyPass::py_help, &PassWrap::default_py_help)
			;

		class_<Initializer>("Initializer");
		scope().attr("_hidden") = new Initializer();

		class_<IdString>("IdString")
			.def(init<std::string>())
			.def(boost::python::self_ns::str(boost::python::self_ns::self))
			.def(boost::python::self_ns::repr(boost::python::self_ns::self))
			.def("get_reference", &IdString::get_reference)
			.def("put_reference", &IdString::put_reference)
			.def("str", &IdString::str)
			.def("substr", &IdString::substr)
			.def("size", &IdString::size)
			.def("empty", &IdString::empty)
			.def("clear", &IdString::clear)
			.def("hash", &IdString::hash)
			.def("in_IdString", &IdString::in_IdString)
			.def("in_std_string", &IdString::in_std_string)
			.def("in_pool_IdString", &IdString::in_pool_IdString)
			.def(self < self)
			.def(self == self)
			.def(self != self)
			;

		class_<Const>("Const")
			.def(boost::python::self_ns::str(boost::python::self_ns::self))
			.def(boost::python::self_ns::repr(boost::python::self_ns::self))
			.def("as_bool", &Const::as_bool)
			.def("as_int", &Const::as_int)
			.def("as_string", &Const::as_string)
			.def("from_string", &Const::from_string)
			.def("decode_string", &Const::decode_string)
			.def("size", &Const::size)
			.def("is_fully_zero", &Const::is_fully_zero)
			.def("is_fully_ones", &Const::is_fully_ones)
			.def("is_fully_def", &Const::is_fully_def)
			.def("is_fully_undef", &Const::is_fully_undef)
			.def("extract", &Const::extract)
			.def("hash", &Const::hash)
			.def(self < self)
			.def(self == self)
			.def(self != self)
			;

		class_<CaseRule>("CaseRule")
			.def(boost::python::self_ns::str(boost::python::self_ns::self))
			.def(boost::python::self_ns::repr(boost::python::self_ns::self))
			.def("clone", &CaseRule::clone)
			;

		class_<SwitchRule>("SwitchRule")
			.def(boost::python::self_ns::str(boost::python::self_ns::self))
			.def(boost::python::self_ns::repr(boost::python::self_ns::self))
			.def("clone", &SwitchRule::clone)
			;

		class_<SyncRule>("SyncRule")
			.def(boost::python::self_ns::str(boost::python::self_ns::self))
			.def(boost::python::self_ns::repr(boost::python::self_ns::self))
			.def("clone", &SyncRule::clone)
			;

		class_<Process>("Process")
			.def(boost::python::self_ns::str(boost::python::self_ns::self))
			.def(boost::python::self_ns::repr(boost::python::self_ns::self))
			.def("clone", &Process::clone)
			;

		class_<SigChunk>("SigChunk")
			.def(boost::python::self_ns::str(boost::python::self_ns::self))
			.def(boost::python::self_ns::repr(boost::python::self_ns::self))
			.def("extract", &SigChunk::extract)
			.def(self < self)
			.def(self == self)
			.def(self != self)
			;

		class_<SigBit>("SigBit")
			.def(boost::python::self_ns::str(boost::python::self_ns::self))
			.def(boost::python::self_ns::repr(boost::python::self_ns::self))
			.def("hash", &SigBit::hash)
			.def(self < self)
			.def(self == self)
			.def(self != self)
			;

		class_<SigSpec>("SigSpec")
			.def(boost::python::self_ns::str(boost::python::self_ns::self))
			.def(boost::python::self_ns::repr(boost::python::self_ns::self))
			.def("get_hash", &SigSpec::get_hash)
			.def("size", &SigSpec::size)
			.def("empty", &SigSpec::empty)
			.def("replace_SigSpec_SigSpec", &SigSpec::replace_SigSpec_SigSpec)
			.def("replace_SigSpec_SigSpec_SigSpec", &SigSpec::replace_SigSpec_SigSpec_SigSpec)
			.def("replace_int_SigSpec", &SigSpec::replace_int_SigSpec)
			.def("remove_SigSpec", &SigSpec::remove_SigSpec)
			.def("remove_SigSpec_SigSpec", &SigSpec::remove_SigSpec_SigSpec)
			.def("remove2_SigSpec_SigSpec", &SigSpec::remove2_SigSpec_SigSpec)
			.def("remove_pool_SigBit", &SigSpec::remove_pool_SigBit)
			.def("remove_pool_SigBit_SigSpec", &SigSpec::remove_pool_SigBit_SigSpec)
			.def("remove2_pool_SigBit_SigSpec", &SigSpec::remove2_pool_SigBit_SigSpec)
			.def("remove_int_int", &SigSpec::remove_int_int)
			.def("extract_SigSpec_SigSpec", &SigSpec::extract_SigSpec_SigSpec)
			.def("extract_pool_SigBit_SigSpec", &SigSpec::extract_pool_SigBit_SigSpec)
			.def("extract_int_int", &SigSpec::extract_int_int)
			.def("append", &SigSpec::append)
			.def("append_bit", &SigSpec::append_bit)
			.def("extend_u0", &SigSpec::extend_u0)
			.def("repeat", &SigSpec::repeat)
			.def("is_wire", &SigSpec::is_wire)
			.def("is_chunk", &SigSpec::is_chunk)
			.def("is_bit", &SigSpec::is_bit)
			.def("is_fully_const", &SigSpec::is_fully_const)
			.def("is_fully_zero", &SigSpec::is_fully_zero)
			.def("is_fully_ones", &SigSpec::is_fully_ones)
			.def("is_fully_def", &SigSpec::is_fully_def)
			.def("is_fully_undef", &SigSpec::is_fully_undef)
			.def("has_const", &SigSpec::has_const)
			.def("has_marked_bits", &SigSpec::has_marked_bits)
			.def("as_bool", &SigSpec::as_bool)
			.def("as_int", &SigSpec::as_int)
			.def("as_string", &SigSpec::as_string)
			.def("as_const", &SigSpec::as_const)
			.def("as_wire", &SigSpec::as_wire)
			.def("as_chunk", &SigSpec::as_chunk)
			.def("as_bit", &SigSpec::as_bit)
			.def("match", &SigSpec::match)
			.def("parse", &SigSpec::parse)
			.def("parse_sel", &SigSpec::parse_sel)
			.def("parse_rhs", &SigSpec::parse_rhs)
			.def("hash", &SigSpec::hash)
			.def("check", &SigSpec::check)
			.def(self < self)
			.def(self == self)
			.def(self != self)
			;

		class_<Cell>("Cell", no_init)
			.def(boost::python::self_ns::str(boost::python::self_ns::self))
			.def(boost::python::self_ns::repr(boost::python::self_ns::self))
			.def("hash", &Cell::hash)
			.def("hasPort", &Cell::hasPort)
			.def("unsetPort", &Cell::unsetPort)
			.def("setPort", &Cell::setPort)
			.def("known", &Cell::known)
			.def("input", &Cell::input)
			.def("output", &Cell::output)
			.def("hasParam", &Cell::hasParam)
			.def("unsetParam", &Cell::unsetParam)
			.def("setParam", &Cell::setParam)
			.def("fixup_parameters", &Cell::fixup_parameters)
			.def("has_keep_attr", &Cell::has_keep_attr)
			;

		class_<Wire>("Wire", no_init)
			.def(boost::python::self_ns::str(boost::python::self_ns::self))
			.def(boost::python::self_ns::repr(boost::python::self_ns::self))
			.def("hash", &Wire::hash)
			;

		class_<Memory>("Memory", no_init)
			.def(boost::python::self_ns::str(boost::python::self_ns::self))
			.def(boost::python::self_ns::repr(boost::python::self_ns::self))
			.def("hash", &Memory::hash)
			;

		class_<Module>("Module")
			.def(boost::python::self_ns::str(boost::python::self_ns::self))
			.def(boost::python::self_ns::repr(boost::python::self_ns::self))
			.def("get_cells", &Module::get_cells)
			.def("get_wires", &Module::get_wires)
			.def("register_monitor", &Module::register_monitor)
			.def("hash", &Module::hash)
			.def("connect_SigSig", &Module::connect_SigSig)
			.def("connect_SigSpec_SigSpec", &Module::connect_SigSpec_SigSpec)
			.def("new_connections", &Module::new_connections)
			.def("cloneInto", &Module::cloneInto)
			.def("has_memories", &Module::has_memories)
			.def("has_processes", &Module::has_processes)
			.def("has_memories_warn", &Module::has_memories_warn)
			.def("has_processes_warn", &Module::has_processes_warn)
			.def("wire", &Module::wire)
			.def("cell", &Module::cell)
			.def("remove_pool_Wire", &Module::remove_pool_Wire)
			.def("remove_Cell", &Module::remove_Cell)
			.def("rename_Wire_IdString", &Module::rename_Wire_IdString)
			.def("rename_Cell_IdString", &Module::rename_Cell_IdString)
			.def("rename_IdString_IdString", &Module::rename_IdString_IdString)
			.def("swap_names_Wire_Wire", &Module::swap_names_Wire_Wire)
			.def("swap_names_Cell_Cell", &Module::swap_names_Cell_Cell)
			.def("uniquify_IdString", &Module::uniquify_IdString)
			.def("uniquify_IdString_int", &Module::uniquify_IdString_int)
			.def("addWire_IdString_int", &Module::addWire_IdString_int)
			.def("addWire_IdString_Wire", &Module::addWire_IdString_Wire)
			.def("addCell_IdString_IdString", &Module::addCell_IdString_IdString)
			.def("addCell_IdString_Cell", &Module::addCell_IdString_Cell)
			.def("addNot", &Module::addNot)
			.def("addPos", &Module::addPos)
			.def("addNeg", &Module::addNeg)
			.def("addAnd", &Module::addAnd)
			.def("addOr", &Module::addOr)
			.def("addXor", &Module::addXor)
			.def("addXnor", &Module::addXnor)
			.def("addReduceAnd", &Module::addReduceAnd)
			.def("addReduceOr", &Module::addReduceOr)
			.def("addReduceXor", &Module::addReduceXor)
			.def("addReduceXnor", &Module::addReduceXnor)
			.def("addReduceBool", &Module::addReduceBool)
			.def("addShl", &Module::addShl)
			.def("addShr", &Module::addShr)
			.def("addSshl", &Module::addSshl)
			.def("addSshr", &Module::addSshr)
			.def("addShift", &Module::addShift)
			.def("addShiftx", &Module::addShiftx)
			.def("addLt", &Module::addLt)
			.def("addLe", &Module::addLe)
			.def("addEq", &Module::addEq)
			.def("addNe", &Module::addNe)
			.def("addEqx", &Module::addEqx)
			.def("addNex", &Module::addNex)
			.def("addGe", &Module::addGe)
			.def("addGt", &Module::addGt)
			.def("addAdd", &Module::addAdd)
			.def("addSub", &Module::addSub)
			.def("addMul", &Module::addMul)
			.def("addDiv", &Module::addDiv)
			.def("addMod", &Module::addMod)
			.def("addPow", &Module::addPow)
			.def("addLogicNot", &Module::addLogicNot)
			.def("addLogicAnd", &Module::addLogicAnd)
			.def("addLogicOr", &Module::addLogicOr)
			.def("addMux", &Module::addMux)
			.def("addPmux", &Module::addPmux)
			.def("addSlice", &Module::addSlice)
			.def("addConcat", &Module::addConcat)
			.def("addLut", &Module::addLut)
			.def("addTribuf", &Module::addTribuf)
			.def("addAssert", &Module::addAssert)
			.def("addAssume", &Module::addAssume)
			.def("addLive", &Module::addLive)
			.def("addFair", &Module::addFair)
			.def("addCover", &Module::addCover)
			.def("addEquiv", &Module::addEquiv)
			.def("addSr", &Module::addSr)
			.def("addFf", &Module::addFf)
			.def("addDff", &Module::addDff)
			.def("addDffe", &Module::addDffe)
			.def("addDffsr", &Module::addDffsr)
			.def("addAdff", &Module::addAdff)
			.def("addDlatch", &Module::addDlatch)
			.def("addDlatchsr", &Module::addDlatchsr)
			.def("addBufGate", &Module::addBufGate)
			.def("addNotGate", &Module::addNotGate)
			.def("addAndGate", &Module::addAndGate)
			.def("addNandGate", &Module::addNandGate)
			.def("addOrGate", &Module::addOrGate)
			.def("addNorGate", &Module::addNorGate)
			.def("addXorGate", &Module::addXorGate)
			.def("addXnorGate", &Module::addXnorGate)
			.def("addAndnotGate", &Module::addAndnotGate)
			.def("addOrnotGate", &Module::addOrnotGate)
			.def("addMuxGate", &Module::addMuxGate)
			.def("addAoi3Gate", &Module::addAoi3Gate)
			.def("addOai3Gate", &Module::addOai3Gate)
			.def("addAoi4Gate", &Module::addAoi4Gate)
			.def("addOai4Gate", &Module::addOai4Gate)
			.def("addFfGate", &Module::addFfGate)
			.def("addDffGate", &Module::addDffGate)
			.def("addDffeGate", &Module::addDffeGate)
			.def("addDffsrGate", &Module::addDffsrGate)
			.def("addAdffGate", &Module::addAdffGate)
			.def("addDlatchGate", &Module::addDlatchGate)
			.def("addDlatchsrGate", &Module::addDlatchsrGate)
			.def("Not", &Module::Not)
			.def("Pos", &Module::Pos)
			.def("Neg", &Module::Neg)
			.def("And", &Module::And)
			.def("Or", &Module::Or)
			.def("Xor", &Module::Xor)
			.def("Xnor", &Module::Xnor)
			.def("ReduceAnd", &Module::ReduceAnd)
			.def("ReduceOr", &Module::ReduceOr)
			.def("ReduceXor", &Module::ReduceXor)
			.def("ReduceXnor", &Module::ReduceXnor)
			.def("ReduceBool", &Module::ReduceBool)
			.def("Shl", &Module::Shl)
			.def("Shr", &Module::Shr)
			.def("Sshl", &Module::Sshl)
			.def("Sshr", &Module::Sshr)
			.def("Shift", &Module::Shift)
			.def("Shiftx", &Module::Shiftx)
			.def("Lt", &Module::Lt)
			.def("Le", &Module::Le)
			.def("Eq", &Module::Eq)
			.def("Ne", &Module::Ne)
			.def("Eqx", &Module::Eqx)
			.def("Nex", &Module::Nex)
			.def("Ge", &Module::Ge)
			.def("Gt", &Module::Gt)
			.def("Add", &Module::Add)
			.def("Sub", &Module::Sub)
			.def("Mul", &Module::Mul)
			.def("Div", &Module::Div)
			.def("Mod", &Module::Mod)
			.def("LogicNot", &Module::LogicNot)
			.def("LogicAnd", &Module::LogicAnd)
			.def("LogicOr", &Module::LogicOr)
			.def("Mux", &Module::Mux)
			.def("Pmux", &Module::Pmux)
			.def("BufGate", &Module::BufGate)
			.def("NotGate", &Module::NotGate)
			.def("AndGate", &Module::AndGate)
			.def("NandGate", &Module::NandGate)
			.def("OrGate", &Module::OrGate)
			.def("NorGate", &Module::NorGate)
			.def("XorGate", &Module::XorGate)
			.def("XnorGate", &Module::XnorGate)
			.def("AndnotGate", &Module::AndnotGate)
			.def("OrnotGate", &Module::OrnotGate)
			.def("MuxGate", &Module::MuxGate)
			.def("Aoi3Gate", &Module::Aoi3Gate)
			.def("Oai3Gate", &Module::Oai3Gate)
			.def("Aoi4Gate", &Module::Aoi4Gate)
			.def("Oai4Gate", &Module::Oai4Gate)
			.def("Anyconst", &Module::Anyconst)
			.def("Anyseq", &Module::Anyseq)
			.def("Allconst", &Module::Allconst)
			.def("Allseq", &Module::Allseq)
			.def("Initstate", &Module::Initstate)
			;

		class_<Design>("Design")
			.def(boost::python::self_ns::str(boost::python::self_ns::self))
			.def(boost::python::self_ns::repr(boost::python::self_ns::self))
			.def("get_modules", &Design::get_modules)
			.def("run", &Design::run)
			.def("register_monitor", &Design::register_monitor)
			.def("hash", &Design::hash)
			.def("module", &Design::module)
			.def("has", &Design::has)
			.def("add", &Design::add)
			.def("addModule", &Design::addModule)
			.def("remove", &Design::remove)
			.def("rename", &Design::rename)
			.def("scratchpad_unset", &Design::scratchpad_unset)
			.def("scratchpad_set_int", &Design::scratchpad_set_int)
			.def("scratchpad_set_bool", &Design::scratchpad_set_bool)
			.def("scratchpad_set_string", &Design::scratchpad_set_string)
			.def("scratchpad_get_int", &Design::scratchpad_get_int)
			.def("scratchpad_get_bool", &Design::scratchpad_get_bool)
			.def("scratchpad_get_string", &Design::scratchpad_get_string)
			.def("selected_module_IdString", &Design::selected_module_IdString)
			.def("selected_whole_module_IdString", &Design::selected_whole_module_IdString)
			.def("selected_member", &Design::selected_member)
			.def("selected_module_Module", &Design::selected_module_Module)
			.def("selected_whole_module_Module", &Design::selected_whole_module_Module)
			.def("full_selection", &Design::full_selection)
			;

		def("escape_id", escape_id);
		def("unescape_id_std_string", unescape_id_std_string);
		def("unescape_id_IdString", unescape_id_IdString);
		def("const_not", const_not);
		def("const_and", const_and);
		def("const_or", const_or);
		def("const_xor", const_xor);
		def("const_xnor", const_xnor);
		def("const_reduce_and", const_reduce_and);
		def("const_reduce_or", const_reduce_or);
		def("const_reduce_xor", const_reduce_xor);
		def("const_reduce_xnor", const_reduce_xnor);
		def("const_reduce_bool", const_reduce_bool);
		def("const_logic_not", const_logic_not);
		def("const_logic_and", const_logic_and);
		def("const_logic_or", const_logic_or);
		def("const_shl", const_shl);
		def("const_shr", const_shr);
		def("const_sshl", const_sshl);
		def("const_sshr", const_sshr);
		def("const_shift", const_shift);
		def("const_shiftx", const_shiftx);
		def("const_lt", const_lt);
		def("const_le", const_le);
		def("const_eq", const_eq);
		def("const_ne", const_ne);
		def("const_eqx", const_eqx);
		def("const_nex", const_nex);
		def("const_ge", const_ge);
		def("const_gt", const_gt);
		def("const_add", const_add);
		def("const_sub", const_sub);
		def("const_mul", const_mul);
		def("const_div", const_div);
		def("const_mod", const_mod);
		def("const_pow", const_pow);
		def("const_pos", const_pos);
		def("const_neg", const_neg);
		def("run",run);
		def("log",log);

	}

}
#endif
