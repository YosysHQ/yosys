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

#include "kernel/yosys.h"

#include "frontends/verific/verific.h"

#ifdef VERIFIC_NAMESPACE
using namespace Verific;
#endif

YOSYS_NAMESPACE_BEGIN

struct VerificExtNets
{
	int portname_cnt = 0;

	// a map from Net to the same Net one level up in the design hierarchy
	std::map<Net*, Net*> net_level_up_drive_up;
	std::map<Net*, Net*> net_level_up_drive_down;

	Net *route_up(Net *net, bool drive_up, Net *final_net = nullptr)
	{
		auto &net_level_up = drive_up ? net_level_up_drive_up : net_level_up_drive_down;

		if (net_level_up.count(net) == 0)
		{
			Netlist *nl = net->Owner();

			// Simply return if Netlist is not unique
			log_assert(nl->NumOfRefs() == 1);

			Instance *up_inst = (Instance*)nl->GetReferences()->GetLast();
			Netlist *up_nl = up_inst->Owner();

			// create new Port
			string name = stringf("___extnets_%d", portname_cnt++);
			Port *new_port = new Port(name.c_str(), drive_up ? DIR_OUT : DIR_IN);
			nl->Add(new_port);
			nl->Buf(net)->Connect(new_port);

			// create new Net in up Netlist
			Net *new_net = final_net;
			if (new_net == nullptr || new_net->Owner() != up_nl) {
				new_net = new Net(name.c_str());
				up_nl->Add(new_net);
			}
			up_inst->Connect(new_port, new_net);

			net_level_up[net] = new_net;
		}

		return net_level_up.at(net);
	}

	Net *route_up(Net *net, bool drive_up, Netlist *dest, Net *final_net = nullptr)
	{
		while (net->Owner() != dest)
			net = route_up(net, drive_up, final_net);
		if (final_net != nullptr)
			log_assert(net == final_net);
		return net;
	}

	Netlist *find_common_ancestor(Netlist *A, Netlist *B)
	{
		std::set<Netlist*> ancestors_of_A;

		Netlist *cursor = A;
		while (1) {
			ancestors_of_A.insert(cursor);
			if (cursor->NumOfRefs() != 1)
				break;
			cursor = ((Instance*)cursor->GetReferences()->GetLast())->Owner();
		}

		cursor = B;
		while (1) {
			if (ancestors_of_A.count(cursor))
				return cursor;
			if (cursor->NumOfRefs() != 1)
				break;
			cursor = ((Instance*)cursor->GetReferences()->GetLast())->Owner();
		}

		log_error("No common ancestor found between %s and %s.\n", get_full_netlist_name(A), get_full_netlist_name(B));
	}

	void run(Netlist *nl)
	{
		MapIter mi, mi2;
		Instance *inst;
		PortRef *pr;

		vector<tuple<Instance*, Port*, Net*>> todo_connect;

		FOREACH_INSTANCE_OF_NETLIST(nl, mi, inst)
			run(inst->View());

		FOREACH_INSTANCE_OF_NETLIST(nl, mi, inst)
		FOREACH_PORTREF_OF_INST(inst, mi2, pr)
		{
			Port *port = pr->GetPort();
			Net *net = pr->GetNet();

			if (!net->IsExternalTo(nl))
				continue;

			if (verific_verbose)
				log("Fixing external net reference on port %s.%s.%s:\n", get_full_netlist_name(nl), inst->Name(), port->Name());

			Netlist *ext_nl = net->Owner();

			if (verific_verbose)
				log(" external net owner: %s\n", get_full_netlist_name(ext_nl));

			Netlist *ca_nl = find_common_ancestor(nl, ext_nl);

			if (verific_verbose)
				log(" common ancestor: %s\n", get_full_netlist_name(ca_nl));

			Net *ca_net = route_up(net, !port->IsOutput(), ca_nl);
			Net *new_net = ca_net;

			if (ca_nl != nl)
			{
				if (verific_verbose)
					log(" net in common ancestor: %s\n", ca_net->Name());

				string name = stringf("___extnets_%d", portname_cnt++);
				new_net = new Net(name.c_str());
				nl->Add(new_net);

				Net *n = route_up(new_net, port->IsOutput(), ca_nl, ca_net);
				log_assert(n == ca_net);
			}

			if (verific_verbose)
				log(" new local net: %s\n", new_net->Name());

			log_assert(!new_net->IsExternalTo(nl));
			todo_connect.push_back(tuple<Instance*, Port*, Net*>(inst, port, new_net));
		}

		for (auto it : todo_connect) {
			get<0>(it)->Disconnect(get<1>(it));
			get<0>(it)->Connect(get<1>(it), get<2>(it));
		}
	}
};

void verific_extnets(const std::map<std::string,Netlist*> &nl_todo)
{
	VerificExtNets worker;
	for (auto nl : nl_todo)
		worker.run(nl.second);
}

YOSYS_NAMESPACE_END
