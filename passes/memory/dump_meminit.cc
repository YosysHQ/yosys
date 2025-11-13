
#include "kernel/yosys.h"
#include "kernel/log_help.h"
#include "libs/sha1/sha1.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct DumpMemInitPass : public Pass
{
    DumpMemInitPass() : Pass("dump_meminit", "convert memory INIT parameters and dump to file") { }

    bool formatted_help() override
    {
        auto *help = PrettyHelp::get_current();
        auto content_root = help->get_root();

        content_root->usage("dump_meminit [options] [selection]");
        content_root->paragraph(
            "Write INIT parameters of selected memories to file.  The INIT parameter is removed, "
            "and the name of the written file is assigned to the INIT_FILE parameter."
        );

        content_root->paragraph(
            "Currently requires memories to have the WIDTH parameter assigned, and will rewrite "
            "undefined bits as 0."
        );

        content_root->option("-prefix <prefix>",
            "add <prefix> to beginning of the output file name.  Will output relative to the "
            "current working directory unless an absolute directory is provided."
        );

        content_root->option("-max_name_length <length>",
            "the written file normally uses the hierarchical name of the memory being written. "
            "If the length of the hierarchical name exceeds <length>, replace it with a SHA1 "
            "message digest instead.  Note that this message digest is always 40 characters "
            "long. Has a default value of 60."
        );
        return true;
    }

    void execute(std::vector<std::string> args, RTLIL::Design *design) override
    {
        std::string prefix = "";
        const int DIGEST_LENGTH = 40;
        int max_name_length = 60;
        size_t argidx;
        for (argidx = 1; argidx < args.size(); argidx++)
        {
            std::string arg = args[argidx];
            if (arg == "-prefix" && argidx+1 < args.size()) {
                prefix = args[++argidx];
                continue;
            }
            if (arg == "-max_name_length" && argidx+1 < args.size()) {
                max_name_length = stoi(args[++argidx]);
                if (max_name_length < DIGEST_LENGTH)
                    log_warning("memories with name length in range (%d, %d) will be extended to %d characters\n",
                                max_name_length, DIGEST_LENGTH, DIGEST_LENGTH);
                continue;
            }
            break;
        }
        extra_args(args, argidx, design, true);

        log_header(design, "Dumping memory INIT values\n");

        for (auto *mod : design->selected_unboxed_modules())
        for (auto *cell : mod->selected_cells())
        {
            // skip if cell has no INIT
            if (!cell->hasParam(ID::INIT))
                continue;

            // construct full hierarchical name
            auto full_name = stringf("%s.%s", RTLIL::unescape_id(mod->name), RTLIL::unescape_id(cell->name));

            // read INIT
            auto init = cell->getParam(ID::INIT);
            cell->unsetParam(ID::INIT);

            // check for shorthand values
            if (init.is_fully_undef()) {
                log_debug("%s -> fully undef\n", full_name);
                cell->setParam(ID::INIT_FILE, Const("X"));
                continue;
            }
            if (init.is_fully_zero()) {
                log_debug("%s -> fully zero\n", full_name);
                cell->setParam(ID::INIT_FILE, Const("0"));
                continue;
            }

            // construct output file name
            string filename = prefix;
            if (GetSize(full_name) > max_name_length)
                filename += sha1(full_name);
            else
                filename += full_name;
            filename += ".mem";
            log_debug("%s -> `%s'\n", full_name, filename);

            // open output file
            cell->setParam(ID::INIT_FILE, Const(filename));
            auto *f = fopen(filename.c_str(), "w");
            if (f == nullptr)
                log_error("Can't open `%s' for writing.\n", filename);

            // write memory to file
            int word_size = cell->getParam(ID::WIDTH).as_int();
            for (auto idx = 0; idx < GetSize(init); idx += word_size) {
                auto val = init.extract(idx, word_size, RTLIL::Sx);
                // split into single hex digits
                // effectively fprintf(f, "%x\n", val.as_int()) but with
                // potentially oversized ints and dynamically sized zero padding
                std::string hex_str;
                hex_str.reserve(word_size / 4);
                for (auto x_idx = 0; x_idx < word_size; x_idx += 4) {
                    auto hex = val.extract(x_idx, 4, RTLIL::Sx).as_int();
                    hex_str.push_back((hex < 10 ? '0' : 'a' - 10) + hex);
                }
                reverse(hex_str.begin(), hex_str.end());
                fprintf(f, "%s\n", hex_str.c_str());
            }

            // close output file
            fclose(f);
        }
    }

} DumpMemInitPass;

PRIVATE_NAMESPACE_END
