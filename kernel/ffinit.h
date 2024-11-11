/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2020  Marcelina Kościelnicka <mwk@0x04.net>
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

#ifndef FFINIT_H
#define FFINIT_H

#include "kernel/yosys.h"
#include "kernel/sigtools.h"

YOSYS_NAMESPACE_BEGIN

struct FfInitVals
{
	const SigMap *sigmap;
	dict<SigBit, std::pair<State,SigBit>> initbits;

	void set(const SigMap *sigmap_, RTLIL::Module *module)
	{
		sigmap = sigmap_;
		initbits.clear();
		for (auto wire : module->wires())
		{
			if (wire->attributes.count(ID::init) == 0)
				continue;

			SigSpec wirebits = (*sigmap)(wire);
			Const initval = wire->attributes.at(ID::init);

			for (int i = 0; i < GetSize(wirebits) && i < GetSize(initval); i++)
			{
				SigBit bit = wirebits[i];
				State val = initval[i];

				if (val != State::S0 && val != State::S1 && bit.wire != nullptr)
					continue;

				if (initbits.count(bit)) {
					if (initbits.at(bit).first != val)
						log_error("Conflicting init values for signal %s (%s = %s != %s).\n",
								log_signal(bit), log_signal(SigBit(wire, i)),
								log_signal(val), log_signal(initbits.at(bit).first));
					continue;
				}

				initbits[bit] = std::make_pair(val,SigBit(wire,i));
			}
		}
	}

	RTLIL::State operator()(RTLIL::SigBit bit) const
	{
		auto it = initbits.find((*sigmap)(bit));
		if (it != initbits.end())
			return it->second.first;
		else
			return State::Sx;
	}

	RTLIL::Const operator()(const RTLIL::SigSpec &sig) const
	{
		RTLIL::Const res;
		for (auto bit : sig)
			res.bits().push_back((*this)(bit));
		return res;
	}

	void set_init(RTLIL::SigBit bit, RTLIL::State val)
	{
		SigBit mbit = (*sigmap)(bit);
		SigBit abit = bit;
		auto it = initbits.find(mbit);
		if (it != initbits.end())
			abit = it->second.second;
		else if (val == State::Sx)
			return;
		log_assert(abit.wire);
		initbits[mbit] = std::make_pair(val,abit);
		auto it2 = abit.wire->attributes.find(ID::init);
		if (it2 != abit.wire->attributes.end()) {
			it2->second.bits()[abit.offset] = val;
			if (it2->second.is_fully_undef())
				abit.wire->attributes.erase(it2);
		} else if (val != State::Sx) {
			Const cval(State::Sx, GetSize(abit.wire));
			cval.bits()[abit.offset] = val;
			abit.wire->attributes[ID::init] = cval;
		}
	}

	void set_init(const RTLIL::SigSpec &sig, RTLIL::Const val)
	{
		log_assert(GetSize(sig) == GetSize(val));
		for (int i = 0; i < GetSize(sig); i++)
			set_init(sig[i], val[i]);
	}

	void remove_init(RTLIL::SigBit bit)
	{
		set_init(bit, State::Sx);
	}

	void remove_init(const RTLIL::SigSpec &sig)
	{
		for (auto bit : sig)
			remove_init(bit);
	}

	void clear()
	{
		initbits.clear();
	}

	FfInitVals (const SigMap *sigmap, RTLIL::Module *module)
	{
		set(sigmap, module);
	}

	FfInitVals () {}
};


YOSYS_NAMESPACE_END

#endif
