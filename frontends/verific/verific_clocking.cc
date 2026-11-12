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

VerificClocking::VerificClocking(VerificImporter *importer, Net *net, bool sva_at_only YS_MAYBE_UNUSED)
{
	module = importer->module;

	log_assert(importer != nullptr);
	log_assert(net != nullptr);

	Instance *inst = net->Driver();

#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
	// Detect condition expression in sva_at_only mode
	if (sva_at_only)
	do {
		Instance *inst_mux = net->Driver();
		if (inst_mux == nullptr || inst_mux->Type() != PRIM_MUX)
			break;

		bool pwr1 = inst_mux->GetInput1()->IsPwr();
		bool pwr2 = inst_mux->GetInput2()->IsPwr();

		if (!pwr1 && !pwr2)
			break;

		Net *sva_net = pwr1 ? inst_mux->GetInput2() : inst_mux->GetInput1();
		if (!verific_is_sva_net(importer, sva_net))
			break;

		inst = sva_net->Driver();
		cond_net = inst_mux->GetControl();
		cond_pol = pwr1;
	} while (0);

	if (inst != nullptr && inst->Type() == PRIM_SVA_AT)
	{
		net = inst->GetInput1();
		body_net = inst->GetInput2();

		inst = net->Driver();

		Instance *body_inst = body_net->Driver();
		if (body_inst != nullptr && body_inst->Type() == PRIM_SVA_DISABLE_IFF) {
			disable_net = body_inst->GetInput1();
			disable_sig = importer->net_map_at(disable_net);
			body_net = body_inst->GetInput2();
		}
	}
	else
	{
		if (sva_at_only)
			return;
	}

	// Use while() instead of if() to work around VIPER #13453
	while (inst != nullptr && inst->Type() == PRIM_SVA_POSEDGE)
	{
		net = inst->GetInput();
		inst = net->Driver();;
	}
#endif
	if (inst != nullptr && inst->Type() == PRIM_INV)
	{
		net = inst->GetInput();
		inst = net->Driver();;
		posedge = false;
	}

	// Detect clock-enable circuit
	do {
		if (inst == nullptr || inst->Type() != PRIM_AND)
			break;

		Net *net_dlatch = inst->GetInput1();
		Instance *inst_dlatch = net_dlatch->Driver();

		if (inst_dlatch == nullptr || inst_dlatch->Type() != PRIM_DLATCHRS)
			break;

		if (!inst_dlatch->GetSet()->IsGnd() || !inst_dlatch->GetReset()->IsGnd())
			break;

		Net *net_enable = inst_dlatch->GetInput();
		Net *net_not_clock = inst_dlatch->GetControl();

		if (net_enable == nullptr || net_not_clock == nullptr)
			break;

		Instance *inst_not_clock = net_not_clock->Driver();

		if (inst_not_clock == nullptr || inst_not_clock->Type() != PRIM_INV)
			break;

		Net *net_clock1 = inst_not_clock->GetInput();
		Net *net_clock2 = inst->GetInput2();

		if (net_clock1 == nullptr || net_clock1 != net_clock2)
			break;

		enable_net = net_enable;
		enable_sig = importer->net_map_at(enable_net);

		net = net_clock1;
		inst = net->Driver();;
	} while (0);

#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
	// Detect condition expression
	do {
		if (body_net == nullptr)
			break;

		Instance *inst_mux = body_net->Driver();

		if (inst_mux == nullptr || inst_mux->Type() != PRIM_MUX)
			break;

		bool pwr1 = inst_mux->GetInput1()->IsPwr();
		bool pwr2 = inst_mux->GetInput2()->IsPwr();

		if (!pwr1 && !pwr2)
			break;

		Net *sva_net = pwr1 ? inst_mux->GetInput2() : inst_mux->GetInput1();
		if (!verific_is_sva_net(importer, sva_net))
			break;

		body_net = sva_net;
		cond_net = inst_mux->GetControl();
		cond_pol = pwr1;
	} while (0);
#endif

	clock_net = net;
	clock_sig = importer->net_map_at(clock_net);

	const char *gclk_attr = clock_net->GetAttValue("gclk");
	if (gclk_attr != nullptr && (!strcmp(gclk_attr, "1") || !strcmp(gclk_attr, "'1'")))
		gclk = true;
}

Cell *VerificClocking::addDff(IdString name, SigSpec sig_d, SigSpec sig_q, Const init_value)
{
	log_assert(GetSize(sig_d) == GetSize(sig_q));

	auto set_init_attribute = [&](SigSpec &s) {
		if (GetSize(init_value) == 0)
			return;
		log_assert(GetSize(s) == GetSize(init_value));
		if (s.is_wire()) {
			s.as_wire()->attributes[ID::init] = init_value;
		} else {
			Wire *w = module->addWire(NEW_ID, GetSize(s));
			w->attributes[ID::init] = init_value;
			module->connect(s, w);
			s = w;
		}
	};

	if (enable_sig != State::S1)
		sig_d = module->Mux(NEW_ID, sig_q, sig_d, enable_sig);

	if (disable_sig != State::S0) {
		log_assert(GetSize(sig_q) == GetSize(init_value));

		if (gclk) {
			Wire *pre_d = module->addWire(NEW_ID, GetSize(sig_d));
			Wire *post_q_w = module->addWire(NEW_ID, GetSize(sig_q));

			Const initval(State::Sx, GetSize(sig_q));
			int offset = 0;
			for (auto c : sig_q.chunks()) {
				if (c.wire && c.wire->attributes.count(ID::init)) {
					Const val = c.wire->attributes.at(ID::init);
					for (int i = 0; i < GetSize(c); i++)
						initval.set(offset+i, val[c.offset+i]);
				}
				offset += GetSize(c);
			}

			if (!initval.is_fully_undef())
				post_q_w->attributes[ID::init] = initval;

			module->addMux(NEW_ID, sig_d, init_value, disable_sig, pre_d);
			module->addMux(NEW_ID, post_q_w, init_value, disable_sig, sig_q);

			SigSpec post_q(post_q_w);
			set_init_attribute(post_q);
			return module->addFf(name, pre_d, post_q);
		}

		set_init_attribute(sig_q);
		return module->addAdff(name, clock_sig, disable_sig, sig_d, sig_q, init_value, posedge);
	}

	if (gclk) {
		set_init_attribute(sig_q);
		return module->addFf(name, sig_d, sig_q);
	}

	set_init_attribute(sig_q);
	return module->addDff(name, clock_sig, sig_d, sig_q, posedge);
}

Cell *VerificClocking::addAdff(IdString name, RTLIL::SigSpec sig_arst, SigSpec sig_d, SigSpec sig_q, Const arst_value)
{
	log_assert(gclk == false);
	log_assert(disable_sig == State::S0);

	// FIXME: Adffe
	if (enable_sig != State::S1)
		sig_d = module->Mux(NEW_ID, sig_q, sig_d, enable_sig);

	return module->addAdff(name, clock_sig, sig_arst, sig_d, sig_q, arst_value, posedge);
}

Cell *VerificClocking::addDffsr(IdString name, RTLIL::SigSpec sig_set, RTLIL::SigSpec sig_clr, SigSpec sig_d, SigSpec sig_q)
{
	log_assert(gclk == false);
	log_assert(disable_sig == State::S0);

	// FIXME: Dffsre
	if (enable_sig != State::S1)
		sig_d = module->Mux(NEW_ID, sig_q, sig_d, enable_sig);

	return module->addDffsr(name, clock_sig, sig_set, sig_clr, sig_d, sig_q, posedge);
}

Cell *VerificClocking::addAldff(IdString name, RTLIL::SigSpec sig_aload, RTLIL::SigSpec sig_adata, SigSpec sig_d, SigSpec sig_q)
{
	log_assert(disable_sig == State::S0);

	// FIXME: Aldffe
	if (enable_sig != State::S1)
		sig_d = module->Mux(NEW_ID, sig_q, sig_d, enable_sig);

	if (gclk) {
		Wire *pre_d = module->addWire(NEW_ID, GetSize(sig_d));
		Wire *post_q = module->addWire(NEW_ID, GetSize(sig_q));

		Const initval(State::Sx, GetSize(sig_q));
		int offset = 0;
		for (auto c : sig_q.chunks()) {
			if (c.wire && c.wire->attributes.count(ID::init)) {
				Const val = c.wire->attributes.at(ID::init);
				for (int i = 0; i < GetSize(c); i++)
					initval.set(offset+i, val[c.offset+i]);
			}
			offset += GetSize(c);
		}

		if (!initval.is_fully_undef())
			post_q->attributes[ID::init] = initval;

		module->addMux(NEW_ID, sig_d, sig_adata, sig_aload, pre_d);
		module->addMux(NEW_ID, post_q, sig_adata, sig_aload, sig_q);

		return module->addFf(name, pre_d, post_q);
	}

	return module->addAldff(name, clock_sig, sig_aload, sig_d, sig_q, sig_adata, posedge);
}

YOSYS_NAMESPACE_END
