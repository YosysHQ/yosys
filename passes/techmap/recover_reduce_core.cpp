/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2017 Robert Ou <rqou@robertou.com>
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

struct RecoverReduceCorePass : public Pass {
    enum GateType {
        And,
        Or,
        Xor
    };

    RecoverReduceCorePass() : Pass("recover_reduce_core", "converts gate chains into $reduce_*") { }
    virtual void help()
    {
        //   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
        log("\n");
        log("    recover_reduce_core\n");
        log("\n");
        log("converts gate chains into $reduce_*\n");
        log("\n");
        log("This performs the core step of the recover_reduce command. This step recognizes\n");
        log("chains of gates found by the previous steps and converts these chains into one\n");
        log("logical cell.\n");
        log("\n");
    }
    virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
    {
        (void)args;

        for (auto module : design->selected_modules())
        {
            SigMap sigmap(module);

            // Index all of the nets in the module
            dict<SigBit, Cell*> sig_to_driver;
            dict<SigBit, pool<Cell*>> sig_to_sink;
            for (auto cell : module->selected_cells())
            {
                for (auto &conn : cell->connections())
                {
                    if (cell->output(conn.first))
                        for (auto bit : sigmap(conn.second))
                            sig_to_driver[bit] = cell;

                    if (cell->input(conn.first))
                    {
                        for (auto bit : sigmap(conn.second))
                        {
                            if (sig_to_sink.count(bit) == 0)
                                sig_to_sink[bit] = pool<Cell*>();
                            sig_to_sink[bit].insert(cell);
                        }
                    }
                }
            }

            // Need to check if any wires connect to module ports
            pool<SigBit> port_sigs;
            for (auto wire : module->selected_wires())
                if (wire->port_input || wire->port_output)
                    for (auto bit : sigmap(wire))
                        port_sigs.insert(bit);

            // Actual logic starts here
            pool<Cell*> consumed_cells;
            for (auto cell : module->selected_cells())
            {
                if (consumed_cells.count(cell))
                    continue;

                GateType gt;

                if (cell->type == "$_AND_")
                    gt = GateType::And;
                else if (cell->type == "$_OR_")
                    gt = GateType::Or;
                else if (cell->type == "$_XOR_")
                    gt = GateType::Xor;
                else
                    continue;

                log("Working on cell %s...\n", cell->name.c_str());
            }
        }
    }
} RecoverReduceCorePass;

PRIVATE_NAMESPACE_END
