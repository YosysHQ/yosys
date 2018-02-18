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

extern pool<int> verific_sva_prims;

struct VerificImporter;

struct VerificClockEdge {
	Verific::Net *clock_net = nullptr;
	SigBit clock_sig = State::Sx;
	bool posedge = false;
	VerificClockEdge(VerificImporter *importer, Verific::Instance *inst);
};

struct VerificImporter
{
	RTLIL::Module *module;
	Verific::Netlist *netlist;

	std::map<Verific::Net*, RTLIL::SigBit> net_map;
	std::map<Verific::Net*, Verific::Net*> sva_posedge_map;

	bool mode_gates, mode_keep, mode_nosva, mode_nosvapp, mode_names, verbose;

	VerificImporter(bool mode_gates, bool mode_keep, bool mode_nosva, bool mode_nosvapp, bool mode_names, bool verbose);

	RTLIL::SigBit net_map_at(Verific::Net *net);

	void import_attributes(dict<RTLIL::IdString, RTLIL::Const> &attributes, Verific::DesignObj *obj);

	RTLIL::SigSpec operatorInput(Verific::Instance *inst);
	RTLIL::SigSpec operatorInput1(Verific::Instance *inst);
	RTLIL::SigSpec operatorInput2(Verific::Instance *inst);
	RTLIL::SigSpec operatorInport(Verific::Instance *inst, const char *portname);
	RTLIL::SigSpec operatorOutput(Verific::Instance *inst);

	bool import_netlist_instance_gates(Verific::Instance *inst, RTLIL::IdString inst_name);
	bool import_netlist_instance_cells(Verific::Instance *inst, RTLIL::IdString inst_name);

	void merge_past_ffs_clock(pool<RTLIL::Cell*> &candidates, SigBit clock, bool clock_pol);
	void merge_past_ffs(pool<RTLIL::Cell*> &candidates);

	void import_netlist(RTLIL::Design *design, Verific::Netlist *nl, std::set<Verific::Netlist*> &nl_todo);
};


void import_sva_assert(VerificImporter *importer, Verific::Instance *inst);
void import_sva_assume(VerificImporter *importer, Verific::Instance *inst);
void import_sva_cover(VerificImporter *importer, Verific::Instance *inst);

void svapp_assert(Verific::Instance *inst);
void svapp_assume(Verific::Instance *inst);
void svapp_cover(Verific::Instance *inst);

YOSYS_NAMESPACE_END

#endif
