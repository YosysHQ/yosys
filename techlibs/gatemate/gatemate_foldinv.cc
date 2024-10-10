/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2021  gatecat <gatecat@ds0.me>
 *  Copyright (C) 2021  Cologne Chip AG <support@colognechip.com>
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

struct LUTPin {
    int input_bit;
    IdString init_param;
};

struct LUTType {
    dict<IdString, LUTPin> inputs;
    IdString output_param;
};

struct FoldInvWorker {
    FoldInvWorker(Module *module) : module(module), sigmap(module) {};
    Module *module;
    SigMap sigmap;

    // Mapping from inverter output to inverter input
    dict<SigBit, SigBit> inverted_bits;
    // Mapping from inverter input to inverter
    dict<SigBit, Cell*> inverter_input;

    const dict<IdString, LUTType> lut_types = {
        {ID(CC_LUT2), {{
                {ID(I0), {0, ID(INIT)}},
                {ID(I1), {1, ID(INIT)}},
            }, ID(INIT)}},
        {ID(CC_L2T4), {{
                {ID(I0), {0, ID(INIT_L00)}},
                {ID(I1), {1, ID(INIT_L00)}},
                {ID(I2), {0, ID(INIT_L01)}},
                {ID(I3), {1, ID(INIT_L01)}},
            }, ID(INIT_L10)}},
        {ID(CC_L2T5), {{
                {ID(I0), {0, ID(INIT_L02)}},
                {ID(I1), {1, ID(INIT_L02)}},
                {ID(I2), {0, ID(INIT_L03)}},
                {ID(I3), {1, ID(INIT_L03)}},
                {ID(I4), {0, ID(INIT_L20)}},
            }, ID(INIT_L20)}},
    };


    void find_inverted_bits()
    {
        for (auto cell : module->selected_cells()) {
            if (cell->type != ID($__CC_NOT))
                continue;
            SigBit a = sigmap(cell->getPort(ID::A)[0]);
            SigBit y = sigmap(cell->getPort(ID::Y)[0]);
            inverted_bits[y] = a;
            inverter_input[a] = cell;
        }
    }

    Const invert_lut_input(Const lut, int bit)
    {
        Const result(State::S0, GetSize(lut));
        for (int i = 0; i < GetSize(lut); i++) {
            int j = i ^ (1 << bit);
            result.bits()[j] = lut[i];
        }
        return result;
    }

    Const invert_lut_output(Const lut)
    {
        Const result(State::S0, GetSize(lut));
        for (int i = 0; i < GetSize(lut); i++)
            result.bits()[i] = (lut[i] == State::S1) ? State::S0 : State::S1;
        return result;
    }

    void fold_input_inverters()
    {
        for (auto cell : module->selected_cells()) {
            auto found_type = lut_types.find(cell->type);
            if (found_type == lut_types.end())
                continue;
            const auto &type = found_type->second;
            for (const auto &ipin : type.inputs) {
                if (!cell->hasPort(ipin.first))
                    continue;
                auto sig = cell->getPort(ipin.first);
                if (GetSize(sig) == 0)
                    continue;
                SigBit bit = sigmap(sig[0]);
                auto inv = inverted_bits.find(bit);
                if (inv == inverted_bits.end())
                    continue; // not the output of an inverter
                // Rewire to inverter input
                cell->unsetPort(ipin.first);
                cell->setPort(ipin.first, inv->second);
                // Rewrite init
                cell->setParam(ipin.second.init_param,
                    invert_lut_input(cell->getParam(ipin.second.init_param), ipin.second.input_bit));
            }
        }
    }

    void fold_output_inverters()
    {
        pool<SigBit> used_bits;
        // Find bits that are actually used
        for (auto cell : module->selected_cells()) {
            for (auto conn : cell->connections()) {
                if (cell->output(conn.first))
                    continue;
                for (auto bit : sigmap(conn.second))
                    used_bits.insert(bit);
            }
        }
        // Find LUTs driving inverters
        // (create a vector to avoid iterate-and-modify issues)
        std::vector<std::pair<Cell *, Cell*>> lut_inv;
        for (auto cell : module->selected_cells()) {
            auto found_type = lut_types.find(cell->type);
            if (found_type == lut_types.end())
                continue;
            if (!cell->hasPort(ID::O))
                continue;
            auto o_sig = cell->getPort(ID::O);
            if (GetSize(o_sig) == 0)
                continue;
            SigBit o = sigmap(o_sig[0]);
            auto found_inv = inverter_input.find(o);
            if (found_inv == inverter_input.end())
                continue; // doesn't drive an inverter
            lut_inv.emplace_back(cell, found_inv->second);
        }
        for (auto pair : lut_inv) {
            Cell *orig_lut = pair.first;
            Cell *inv = pair.second;
            // Find the inverter output
            SigBit inv_y = sigmap(inv->getPort(ID::Y)[0]);
            // Inverter output might not actually be used; if all users were folded into inputs already
            if (!used_bits.count(inv_y))
                continue;
            // Create a duplicate of the LUT with an inverted output
            // (if the uninverted version becomes unused it will be swept away)
            Cell *dup_lut = module->addCell(NEW_ID, orig_lut->type);
            inv->unsetPort(ID::Y);
            dup_lut->setPort(ID::O, inv_y);
            for (auto conn : orig_lut->connections()) {
                if (conn.first == ID::O)
                    continue;
                dup_lut->setPort(conn.first, conn.second);
            }
            for (auto param : orig_lut->parameters) {
                if (param.first == lut_types.at(orig_lut->type).output_param)
                    dup_lut->parameters[param.first] = invert_lut_output(param.second);
                else
                    dup_lut->parameters[param.first] = param.second;
            }
        }
    }

    void operator()()
    {
        find_inverted_bits();
        fold_input_inverters();
        fold_output_inverters();
    }
};

struct GatemateFoldInvPass : public Pass {
    GatemateFoldInvPass() : Pass("gatemate_foldinv", "fold inverters into Gatemate LUT trees") { }
    void help() override
    {
        //   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
        log("\n");
        log("    gatemate_foldinv [selection]\n");
        log("\n");
        log("\n");
        log("This pass searches for $__CC_NOT cells and folds them into CC_LUT2, CC_L2T4\n");
        log("and CC_L2T5 cells as created by LUT tree mapping.\n");
        log("\n");
    }

    void execute(std::vector<std::string> args, RTLIL::Design *design) override
    {
        log_header(design, "Executing GATEMATE_FOLDINV pass (folding LUT tree inverters).\n");

        size_t argidx = 1;
        extra_args(args, argidx, design);

        for (Module *module : design->selected_modules()) {
            FoldInvWorker worker(module);
            worker();
        }        
    }
} GatemateFoldInvPass;

PRIVATE_NAMESPACE_END

