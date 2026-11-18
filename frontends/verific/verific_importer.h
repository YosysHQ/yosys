/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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

#ifndef VERIFIC_IMPORTER_H
#define VERIFIC_IMPORTER_H

#ifdef YOSYS_ENABLE_VERIFIC

#include "kernel/yosys.h"

#include "DataBase.h"

YOSYS_NAMESPACE_BEGIN

struct VerificImporter
{
private:
	void recurse_mem_dimensions(RTLIL::Module *module, RTLIL::Memory *memory, Verific::Net *net, const char *&ascii_initdata, int max_bits_in_addr, const RTLIL::SigSpec &prefix, Verific::TypeRange *typeRange = nullptr);
public:
	RTLIL::Module *module;
	Verific::Netlist *netlist;

	std::map<Verific::Net*, RTLIL::SigBit> net_map;
	std::map<Verific::Net*, Verific::Net*> sva_posedge_map;
	pool<Verific::Net*> any_all_nets;

	bool mode_gates, mode_keep, mode_nosva, mode_sva_continue, mode_names, mode_verific;
	bool mode_autocover, mode_fullinit;

	int num_sva_continue = 0;

	VerificImporter(bool mode_gates, bool mode_keep, bool mode_nosva, bool mode_sva_continue, bool mode_names, bool mode_verific, bool mode_autocover, bool mode_fullinit);

	RTLIL::SigBit net_map_at(Verific::Net *net);

	RTLIL::IdString new_verific_id(Verific::DesignObj *obj);
	void import_attributes(dict<RTLIL::IdString, RTLIL::Const> &attributes, Verific::DesignObj *obj, Verific::Netlist  *nl = nullptr, int wire_width_hint = -1);

	RTLIL::SigBit netToSigBit(Verific::Net *net);
	RTLIL::SigSpec operatorInput(Verific::Instance *inst);
	RTLIL::SigSpec operatorInput1(Verific::Instance *inst);
	RTLIL::SigSpec operatorInput2(Verific::Instance *inst);
	RTLIL::SigSpec operatorInport(Verific::Instance *inst, const char *portname);
	RTLIL::SigSpec operatorInportCase(Verific::Instance *inst, const char *portname);
	RTLIL::SigSpec operatorOutput(Verific::Instance *inst, const pool<Verific::Net*> *any_all_nets = nullptr);

	bool import_netlist_instance_gates(Verific::Instance *inst, RTLIL::IdString inst_name);
	bool import_netlist_instance_cells(Verific::Instance *inst, RTLIL::IdString inst_name);

	void merge_past_ffs_clock(pool<RTLIL::Cell*> &candidates, SigBit clock, bool clock_pol);
	void merge_past_ffs(pool<RTLIL::Cell*> &candidates);

	void import_netlist(RTLIL::Design *design, Verific::Netlist *nl, std::map<std::string,Verific::Netlist*> &nl_todo, bool norename = false);
};

YOSYS_NAMESPACE_END

#endif
#endif
