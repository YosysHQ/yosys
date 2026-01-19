/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2024  Miodrag Milanovic <micko@yosyshq.com>
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
#include "kernel/sigtools.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

static SigBit get_bit_or_zero(const SigSpec &sig)
{
	if (GetSize(sig) == 0)
		return State::S0;
	return sig[0];
}

static void nx_carry_chain(Module *module)
{
	SigMap sigmap(module);

	dict<SigBit,Cell*> carry;
	for (auto cell : module->cells())
	{
		if (cell->type == ID(NX_CY_1BIT)) {
			if (cell->getParam(ID(first)).as_int() == 1) continue;
			if (!cell->hasPort(ID(CI)))
				log_error("Not able to find connected carry.\n");
			SigBit ci = sigmap(cell->getPort(ID(CI)).as_bit());
			carry[ci] = cell;
		}
	}

	dict<Cell*,vector<Cell*>> carry_chains;
	log("Detecting carry chains\n");
	for (auto cell : module->cells())
	{
		if (cell->type == ID(NX_CY_1BIT)) {
			if (cell->getParam(ID(first)).as_int() == 0) continue;
			
			vector<Cell*> chain;
			Cell *current = cell;
			chain.push_back(current);

			SigBit co = sigmap(cell->getPort(ID(CO)).as_bit());
			while (co.is_wire())
			{
				if (carry.count(co)==0)
					break;
					//log_error("Not able to find connected carry.\n");
				current = carry[co];
				chain.push_back(current);
				if (!current->hasPort(ID(CO))) break;
				co = sigmap(current->getPort(ID(CO)).as_bit());
			}
			carry_chains[cell] = chain;
		}
	}

	log("Creating NX_CY cells.\n");
	for(auto& c : carry_chains) {
		Cell *cell = nullptr;
		int j = 0;
		int cnt = 0;
		IdString names_A[] = { ID(A1), ID(A2), ID(A3), ID(A4) };
		IdString names_B[] = { ID(B1), ID(B2), ID(B3), ID(B4) };
		IdString names_S[] = { ID(S1), ID(S2), ID(S3), ID(S4) };
		if (!c.second.at(0)->getPort(ID(CI)).is_fully_const()) {
			cell = module->addCell(NEW_ID, ID(NX_CY));
			cell->setParam(ID(add_carry), Const(1,2));
			cell->setPort(ID(CI), State::S1);

			cell->setPort(names_A[0], c.second.at(0)->getPort(ID(CI)).as_bit());
			cell->setPort(names_B[0], State::S0);
			j++;
		}

		for (size_t i=0 ; i<c.second.size(); i++) {
			if (j==0) {
				cell = module->addCell(NEW_ID, ID(NX_CY));
				SigBit ci = c.second.at(i)->getPort(ID(CI)).as_bit();
				cell->setPort(ID(CI), ci);
				if (ci.is_wire()) {
					cell->setParam(ID(add_carry), Const(2,2));
				} else {
					if (ci == State::S0)
						cell->setParam(ID(add_carry), Const(0,2));
					else
						cell->setParam(ID(add_carry), Const(1,2));
				}
			}
			if (j==3) {
				if (cnt !=0 && (cnt % 24 == 0)) {
					SigBit new_co = module->addWire(NEW_ID);
					cell->setPort(ID(A4), State::S0);
					cell->setPort(ID(B4), State::S0);
					cell->setPort(ID(S4), new_co);
					cell = module->addCell(NEW_ID, ID(NX_CY));
					cell->setParam(ID(add_carry), Const(1,2));
					cell->setPort(ID(CI), State::S1);
					cell->setPort(ID(A1), new_co);
					cell->setPort(ID(B1), State::S0);
					j = 1;
				} else {
					if (c.second.at(i)->hasPort(ID(CO)))
						cell->setPort(ID(CO), c.second.at(i)->getPort(ID(CO)));
				}
				cnt++;
			}
			cell->setPort(names_A[j], get_bit_or_zero(c.second.at(i)->getPort(ID(A))));
			cell->setPort(names_B[j], get_bit_or_zero(c.second.at(i)->getPort(ID(B))));
			
			if (c.second.at(i)->hasPort(ID(S))) 
				cell->setPort(names_S[j], c.second.at(i)->getPort(ID(S)));

			j = (j + 1) % 4;
			module->remove(c.second.at(i));
		}
	}
}

struct NXCarryPass : public Pass {
	NXCarryPass() : Pass("nx_carry", "NanoXplore: create carry cells") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    nx_carry [options] [selection]\n");
		log("\n");
		log("Fixes carry chain if needed, break it on 24 elements and group by 4 into NX_CY.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing NX_CARRY pass.\n");
		
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
			nx_carry_chain(module);
	}
} NXCarryPass;

PRIVATE_NAMESPACE_END
