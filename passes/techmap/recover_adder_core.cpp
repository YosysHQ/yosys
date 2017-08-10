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

struct RecoverAdderCorePass : public Pass {
    RecoverAdderCorePass() : Pass("recover_adder_core", "converts adder chains into $alu/$add/$sub") { }
    virtual void help()
    {
        log("\n");
        log("    recover_adder_core\n");
        log("\n");
        log("converts adder chains into $alu/$add/$sub\n");
        log("\n");
        log("This performs the core step of the recover_adder command. This step recognizes\n");
        log("chains of adders found by the previous steps and converts these chains into one\n");
        log("logical cell.");
        log("\n");
    }
    virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
    {
        (void)args;

        for (auto module : design->selected_modules())
        {
            SigMap sigmap(module);

            // Find all the adder/subtractor cells from the previous extract step
            pool<Cell*> addsub_cells;
            for (auto cell : module->selected_cells())
            {
                if (cell->type == "\\HALF_ADDER" || cell->type == "\\FULL_ADDER" ||
                    cell->type == "\\HALF_SUBTRACTOR" || cell->type == "\\FULL_SUBTRACTOR")
                {
                    log("Found adder/subtractor cell %s\n", cell->name.c_str());
                    addsub_cells.insert(cell);
                }
            }

            // Find all the carry-related wires
            dict<SigBit, pool<Cell*>> carry_wires;
            for (auto cell : addsub_cells)
            {
                if (cell->type == "\\HALF_ADDER")
                {
                    auto w = sigmap(cell->getPort("\\Cout"));
                    log_assert(w.size() == 1);
                    carry_wires[w[0]] = pool<Cell*>();
                }
                else if (cell->type == "\\HALF_SUBTRACTOR")
                {
                    auto w = sigmap(cell->getPort("\\Bout"));
                    log_assert(w.size() == 1);
                    carry_wires[w[0]] = pool<Cell*>();
                }
                else if (cell->type == "\\FULL_ADDER")
                {
                    auto w = sigmap(cell->getPort("\\Cout"));
                    log_assert(w.size() == 1);
                    carry_wires[w[0]] = pool<Cell*>();

                    w = sigmap(cell->getPort("\\Cin"));
                    log_assert(w.size() == 1);
                    carry_wires[w[0]] = pool<Cell*>();
                }
                else if (cell->type == "\\FULL_SUBTRACTOR")
                {
                    auto w = sigmap(cell->getPort("\\Bout"));
                    log_assert(w.size() == 1);
                    carry_wires[w[0]] = pool<Cell*>();

                    w = sigmap(cell->getPort("\\Bin"));
                    log_assert(w.size() == 1);
                    carry_wires[w[0]] = pool<Cell*>();
                }
                else
                {
                    log_assert(0);
                }
            }

            // Find all the other cells that touch each carry wire
            for (auto cell : module->selected_cells())
            {
                for (auto &conn: cell->connections())
                {
                    // FIXME: Do we care about checking multiple drivers?
                    if (carry_wires.count(sigmap(conn.second)))
                    {
                        log("Carry wire goes into cell %s\n", cell->name.c_str());
                        carry_wires[sigmap(conn.second)].insert(cell);
                    }
                }
            }

            // Do the actual adder extraction logic
            pool<Cell*> consumed_cells;
            for (auto cell : addsub_cells)
            {
                if (consumed_cells.count(cell))
                    continue;

                log("Working on cell %s...\n", cell->name.c_str());

                bool is_sub = (cell->type == "\\HALF_SUBTRACTOR" || cell->type == "\\FULL_SUBTRACTOR");
                bool has_carryin = false;
                bool has_carryout = false;
                bool has_carry_fanout = false;
                std::deque<Cell*> cur_adder = {cell};

                // Extend "left"
                Cell* x = cell;
                while (true)
                {
                    // This has to be the first bit
                    if (x->type == "\\HALF_ADDER" || x->type == "\\HALF_SUBTRACTOR")
                        break;

                    auto c = sigmap(x->getPort(is_sub ? "\\Bin" : "\\Cin"))[0];
                    // What else is connected to this wire?
                    pool<Cell*> other_carry_cells = pool<Cell*>(carry_wires[c]);
                    other_carry_cells.erase(x);

                    size_t connected_addsubs = 0;
                    Cell* connected_addsub = 0;
                    for (auto y : other_carry_cells)
                    {
                        if (is_sub)
                        {
                            if (y->type == "\\HALF_SUBTRACTOR" || y->type == "\\FULL_SUBTRACTOR")
                            {
                                connected_addsub = y;
                                connected_addsubs++;
                            }
                        }
                        else
                        {
                            if (y->type == "\\HALF_ADDER" || y->type == "\\FULL_ADDER")
                            {
                                connected_addsub = y;
                                connected_addsubs++;
                            }
                        }
                    }
                    log("  This cell is connected to %zu/%zu cells\n", connected_addsubs, other_carry_cells.size());

                    if (connected_addsubs == 0)
                    {
                        // This has to be the end of the chain
                        if (other_carry_cells.size())
                            has_carryin = true;
                        else
                            // This is fine, but how did this happen?
                            log_warning("  Something weird happened?");

                        break;
                    }
                    else
                    {
                        if (connected_addsubs > 1)
                        {
                            // Break the chain here
                            // FIXME: Do we want to find the "longest" adder? Do we do that in a later pass instead?
                            has_carryin = true;
                            break;
                        }
                        else
                        {
                            // The cell we are examining is connected to one and only one other adder/subtractor cell
                            if (other_carry_cells.size() > 1)
                                has_carry_fanout = true;

                            log("  Absorbing cell %s (left)\n", connected_addsub->name.c_str());
                            cur_adder.push_front(connected_addsub);
                            x = connected_addsub;
                        }
                    }
                }

                // Extend "right"
                // FIXME: Deduplicate code?
                x = cell;
                while (true)
                {
                    // This has to be the last bit
                    if (x->type == "\\XOR3")
                        break;

                    auto c = sigmap(x->getPort(is_sub ? "\\Bout" : "\\Cout"))[0];
                    // What else is connected to this wire?
                    pool<Cell*> other_carry_cells = pool<Cell*>(carry_wires[c]);
                    other_carry_cells.erase(x);

                    size_t connected_addsubs = 0;
                    Cell* connected_addsub = 0;
                    for (auto y : other_carry_cells)
                    {
                        if (is_sub)
                        {
                            if (y->type == "\\XOR3" || y->type == "\\FULL_SUBTRACTOR")
                            {
                                connected_addsub = y;
                                connected_addsubs++;
                            }
                        }
                        else
                        {
                            if (y->type == "\\XOR3" || y->type == "\\FULL_ADDER")
                            {
                                connected_addsub = y;
                                connected_addsubs++;
                            }
                        }
                    }
                    log("  This cell is connected to %zu/%zu cells\n", connected_addsubs, other_carry_cells.size());

                    if (connected_addsubs == 0)
                    {
                        // This has to be the end of the chain
                        if (other_carry_cells.size())
                            has_carryout = true;
                        else
                            // This is fine, but how did this happen?
                            log_warning("  Something weird happened?");

                        break;
                    }
                    else
                    {
                        if (connected_addsubs > 1)
                        {
                            // Break the chain here
                            // FIXME: Do we want to find the "longest" adder? Do we do that in a later pass instead?
                            has_carryout = true;
                            break;
                        }
                        else
                        {
                            // The cell we are examining is connected to one and only one other adder/subtractor cell
                            if (other_carry_cells.size() > 1)
                                has_carry_fanout = true;

                            log("  Absorbing cell %s (right)\n", connected_addsub->name.c_str());
                            cur_adder.push_back(connected_addsub);
                            x = connected_addsub;
                        }
                    }
                }

                if (cur_adder.size() > 1)
                {
                    // We found an actual adder
                    log("An adder/subtractor was found!\n");
                    log("  Add/sub: %s\n", is_sub ? "sub" : "add");
                    log("  Carry-in: %s\n", has_carryin ? "yes" : "no");
                    log("  Carry-out: %s\n", has_carryin ? "yes" : "no");
                    log("  Carry fanouts: %s\n", has_carryin ? "yes" : "no");
                    for (auto x : cur_adder)
                        log("    %s\n", x->name.c_str());

                    if (!has_carryin && !has_carry_fanout)
                    {
                        // Can generate an $add/$sub cell
                        SigSpec a;
                        SigSpec b;
                        SigSpec y;

                        for (auto x : cur_adder)
                        {
                            a.append_bit(x->getPort("\\A")[0]);
                            b.append_bit(x->getPort("\\B")[0]);
                            y.append_bit(x->getPort("\\Y")[0]);
                        }

                        if (has_carryout)
                        {
                            if (!is_sub)
                            {
                                y.append_bit(cur_adder.back()->getPort("\\Cout")[0]);
                            }
                            else
                            {
                                // TODO
                                log_assert(0);
                            }
                        }

                        auto addsub_new_cell = module->addCell(NEW_ID, is_sub ? "$sub" : "$add");
                        addsub_new_cell->setParam("\\A_SIGNED", 0);
                        addsub_new_cell->setParam("\\B_SIGNED", 0);
                        addsub_new_cell->setParam("\\A_WIDTH", a.size());
                        addsub_new_cell->setParam("\\B_WIDTH", b.size());
                        addsub_new_cell->setParam("\\Y_WIDTH", y.size());
                        addsub_new_cell->setPort("\\A", a);
                        addsub_new_cell->setPort("\\B", b);
                        addsub_new_cell->setPort("\\Y", y);
                    }
                    else
                    {
                        // Generate an $alu cell
                        log_assert(0);
                        // NOT IMPLEMENTED YET
                    }

                    // Mark all of these cells as removed
                    for (auto x : cur_adder)
                        consumed_cells.insert(x);
                }
            }

            // Remove every cell that we've used up
            for (auto cell : consumed_cells)
                module->remove(cell);
        }
    }
} RecoverAdderCorePass;

PRIVATE_NAMESPACE_END
