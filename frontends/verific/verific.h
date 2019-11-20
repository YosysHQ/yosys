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

#ifdef YOSYS_ENABLE_VERIFIC

#include "DataBase.h"

YOSYS_NAMESPACE_BEGIN

extern int verific_verbose;

extern bool verific_import_pending;
extern void verific_import(Design *design, const std::map<std::string,std::string> &parameters, std::string top = std::string());

extern pool<int> verific_sva_prims;

struct VerificImporter;

struct VerificClocking {
	RTLIL::Module *module = nullptr;
	Verific::Net *clock_net = nullptr;
	Verific::Net *enable_net = nullptr;
	Verific::Net *disable_net = nullptr;
	Verific::Net *body_net = nullptr;
	Verific::Net *cond_net = nullptr;
	SigBit clock_sig = State::Sx;
	SigBit enable_sig = State::S1;
	SigBit disable_sig = State::S0;
	bool posedge = true;
	bool gclk = false;

	VerificClocking() { }
	VerificClocking(VerificImporter *importer, Verific::Net *net, bool sva_at_only = false);
	RTLIL::Cell *addDff(IdString name, SigSpec sig_d, SigSpec sig_q, Const init_value = Const());
	RTLIL::Cell *addAdff(IdString name, RTLIL::SigSpec sig_arst, SigSpec sig_d, SigSpec sig_q, Const arst_value);
	RTLIL::Cell *addDffsr(IdString name, RTLIL::SigSpec sig_set, RTLIL::SigSpec sig_clr, SigSpec sig_d, SigSpec sig_q);

	bool property_matches_sequence(const VerificClocking &seq) const {
		if (clock_net != seq.clock_net)
			return false;
		if (enable_net != seq.enable_net)
			return false;
		if (posedge != seq.posedge)
			return false;
		return true;
	}
};

struct VerificImporter
{
	RTLIL::Module *module;
	Verific::Netlist *netlist;

	std::map<Verific::Net*, RTLIL::SigBit> net_map;
	std::map<Verific::Net*, Verific::Net*> sva_posedge_map;
	pool<Verific::Net*, hash_ptr_ops> any_all_nets;

	bool mode_gates, mode_keep, mode_nosva, mode_names, mode_verific;
	bool mode_autocover, mode_fullinit;

	VerificImporter(bool mode_gates, bool mode_keep, bool mode_nosva, bool mode_names, bool mode_verific, bool mode_autocover, bool mode_fullinit);

	RTLIL::SigBit net_map_at(Verific::Net *net);

	RTLIL::IdString new_verific_id(Verific::DesignObj *obj);
	void import_attributes(dict<RTLIL::IdString, RTLIL::Const> &attributes, Verific::DesignObj *obj);

	RTLIL::SigSpec operatorInput(Verific::Instance *inst);
	RTLIL::SigSpec operatorInput1(Verific::Instance *inst);
	RTLIL::SigSpec operatorInput2(Verific::Instance *inst);
	RTLIL::SigSpec operatorInport(Verific::Instance *inst, const char *portname);
	RTLIL::SigSpec operatorOutput(Verific::Instance *inst, const pool<Verific::Net*, hash_ptr_ops> *any_all_nets = nullptr);

	bool import_netlist_instance_gates(Verific::Instance *inst, RTLIL::IdString inst_name);
	bool import_netlist_instance_cells(Verific::Instance *inst, RTLIL::IdString inst_name);

	void merge_past_ffs_clock(pool<RTLIL::Cell*> &candidates, SigBit clock, bool clock_pol);
	void merge_past_ffs(pool<RTLIL::Cell*> &candidates);

	void import_netlist(RTLIL::Design *design, Verific::Netlist *nl, std::set<Verific::Netlist*> &nl_todo, bool norename = false);
};

void verific_import_sva_assert(VerificImporter *importer, Verific::Instance *inst);
void verific_import_sva_assume(VerificImporter *importer, Verific::Instance *inst);
void verific_import_sva_cover(VerificImporter *importer, Verific::Instance *inst);
void verific_import_sva_trigger(VerificImporter *importer, Verific::Instance *inst);
bool verific_is_sva_net(VerificImporter *importer, Verific::Net *net);

extern int verific_sva_fsm_limit;

YOSYS_NAMESPACE_END

#endif
