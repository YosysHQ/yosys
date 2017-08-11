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

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct RecoverReducePass : public ScriptPass
{
    RecoverReducePass() : ScriptPass("recover_reduce", "recovers $reduce_* from gates") {}
    virtual void help() YS_OVERRIDE
    {
        //   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
        log("\n");
        log("    recover_reduce [options]\n");
        log("\n");
        log("recovers $reduce_* from gates\n");
        log("\n");
        log("Reconstructs $reduce_* elements (e.g. larger gates) given a netlist of gates.");
        log("This pass is intended to be used as part of a circuit reverse-engineering workflow.\n");
        log("\n");
        log("\n");
        log("The following commands are executed by this command:\n");
        help_script();
        log("\n");
    }

    bool one_pass, no_final_abc;

    virtual void clear_flags() YS_OVERRIDE
    {
        one_pass = false;
        no_final_abc = false;
    }

    virtual void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
    {
        clear_flags();

        size_t argidx;
        for (argidx = 1; argidx < args.size(); argidx++)
        {
            if (args[argidx] == "-one_pass") {
                one_pass = true;
                continue;
            }
            if (args[argidx] == "-no_final_abc") {
                no_final_abc = true;
                continue;
            }
            break;
        }
        extra_args(args, argidx, design);

        log_header(design, "Executing recover_reduce.\n");
        log_push();

        run_script(design, "", "");

        log_pop();
    }

    virtual void script() YS_OVERRIDE
    {
        if (!one_pass)
        {
            // Certain structures such as counters seem to work better if we extract only AND
            // and then run a general extract pass.
            // XXX: Why is that? Does this work in general?
            run("abc -g AND");
            run("recover_reduce_core");
        }
        run("abc -g AND,OR,XOR");
        run("recover_reduce_core");

        if (!no_final_abc)
            run("abc");

        run("clean");
    }
} RecoverReducePass;

PRIVATE_NAMESPACE_END
