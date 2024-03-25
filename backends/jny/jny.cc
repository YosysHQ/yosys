/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Aki "lethalbit" Van Ness <aki@yosyshq.com> <aki@lethalbit.net>
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

#include "kernel/rtlil.h"
#include "kernel/register.h"
#include "kernel/sigtools.h"
#include "kernel/celltypes.h"
#include "kernel/log.h"
#include <string>
#include <algorithm>
#include <unordered_map>
#include <vector>
#include <sstream>
#include <iterator>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN


struct JnyWriter
{
    private:
        std::ostream &f;
        bool _use_selection;

        // XXX(aki): TODO: this needs to be updated to us
        // dict<T, V> and then coalesce_cells needs to be updated
        // but for now for the PoC this looks to be sufficient
        std::unordered_map<std::string, std::vector<Cell*>> _cells{};

        bool _include_connections;
        bool _include_attributes;
        bool _include_properties;

        string escape_string(string str) {
            std::string newstr;

            auto itr = str.begin();

            for(; itr != str.end(); ++itr) {
                switch (*itr) {
                    case '\\': {
                        newstr += "\\\\";
                        break;
                    } case '\n': {
                        newstr += "\\n";
                        break;
                    } case '\f': {
                        newstr += "\\f";
                        break;
                    } case '\t': {
                        newstr += "\\t";
                        break;
                    } case '\r': {
                        newstr += "\\r";
                        break;
                    } case '\"': {
                        newstr += "\\\"";
                        break;
                    } case '\b': {
                        newstr += "\\b";
                        break;
                    } default: {
                        newstr += *itr;
                    }
                }
            }

            return newstr;
        }

        // XXX(aki): I know this is far from ideal but i'm out of spoons and cant focus so
        // it'll have to do for now,
        void coalesce_cells(Module* mod)
        {
            _cells.clear();
            for (auto cell : mod->cells()) {
                const auto cell_type = escape_string(RTLIL::unescape_id(cell->type));

                if (_cells.find(cell_type) == _cells.end())
                    _cells.emplace(cell_type, std::vector<Cell*>());

                _cells.at(cell_type).push_back(cell);
            }
        }

        // XXX(aki): this is a lazy way to do this i know,,,
        std::string gen_indent(const uint16_t level)
        {
            std::stringstream s;
            for (uint16_t i = 0; i <= level; ++i)
            {
                s << "  ";
            }
            return s.str();
        }

    public:
    JnyWriter(std::ostream &f, bool use_selection, bool connections, bool attributes, bool properties) noexcept:
        f(f), _use_selection(use_selection),
        _include_connections(connections), _include_attributes(attributes), _include_properties(properties)
         { }

    void write_metadata(Design *design, uint16_t indent_level = 0, std::string invk = "")
    {
        log_assert(design != nullptr);

        design->sort();

        f << "{\n";
        f << "  \"$schema\": \"https://raw.githubusercontent.com/YosysHQ/yosys/main/misc/jny.schema.json\",\n";
        f << stringf("  \"generator\": \"%s\",\n", escape_string(yosys_version_str).c_str());
        f << "  \"version\": \"0.0.1\",\n";
        f << "  \"invocation\": \"" << escape_string(invk) << "\",\n";
        f << "  \"features\": [";

        size_t fnum{0};
        if (_include_connections) {
            ++fnum;
            f << "\"connections\"";
        }

        if (_include_attributes) {
            if (fnum > 0)
                f << ", ";
            ++fnum;
            f << "\"attributes\"";
        }

        if (_include_properties) {
            if (fnum > 0)
                f << ", ";
            ++fnum;
            f << "\"properties\"";
        }

        f << "],\n";

        f << "  \"modules\": [\n";

        bool first{true};
        for (auto mod : _use_selection ? design->selected_modules() : design->modules()) {
            if (!first)
                f << ",\n";
            write_module(mod, indent_level + 2);
            first = false;
        }

        f << "\n";
        f << "  ]\n";
        f << "}\n";
    }

    void write_sigspec(const RTLIL::SigSpec& sig, uint16_t indent_level = 0) {
        const auto _indent = gen_indent(indent_level);

        f << _indent << "  {\n";
        f << _indent << "    \"width\": \"" << sig.size() << "\",\n";
        f << _indent << "    \"type\": \"";

        if (sig.is_wire()) {
            f << "wire";
        } else if (sig.is_chunk()) {
            f << "chunk";
        } else if (sig.is_bit()) {
            f << "bit";
        } else {
            f << "unknown";
        }
        f << "\",\n";

        f << _indent << "    \"const\": ";
        if (sig.has_const()) {
            f << "true";
        } else {
            f << "false";
        }

        f << "\n";

        f << _indent << "  }";
    }

    void write_mod_conn(const std::pair<RTLIL::SigSpec, RTLIL::SigSpec>& conn, uint16_t indent_level = 0) {
        const auto _indent = gen_indent(indent_level);
        f << _indent << "  {\n";
        f << _indent << "    \"signals\": [\n";

        write_sigspec(conn.first, indent_level + 2);
        f << ",\n";
        write_sigspec(conn.second, indent_level + 2);
        f << "\n";

        f << _indent << "     ]\n";
        f << _indent << "  }";
    }

    void write_cell_conn(const std::pair<RTLIL::IdString, RTLIL::SigSpec>& sig, uint16_t indent_level = 0) {
        const auto _indent = gen_indent(indent_level);
        f << _indent << "  {\n";
        f << _indent << "    \"name\": \"" << escape_string(RTLIL::unescape_id(sig.first)) << "\",\n";
        f << _indent << "    \"signals\": [\n";

        write_sigspec(sig.second, indent_level + 2);
        f << "\n";

        f << _indent << "     ]\n";
        f << _indent << "  }";
    }

    void write_module(Module* mod, uint16_t indent_level = 0) {
        log_assert(mod != nullptr);

        coalesce_cells(mod);

        const auto _indent = gen_indent(indent_level);

        f << _indent << "{\n";
        f << stringf("  %s\"name\": \"%s\",\n", _indent.c_str(), escape_string(RTLIL::unescape_id(mod->name)).c_str());
        f << _indent << "  \"cell_sorts\": [\n";

        bool first_sort{true};
        for (auto& sort : _cells) {
            if (!first_sort)
                f << ",\n";
            write_cell_sort(sort, indent_level + 2);
            first_sort = false;
        }
        f << "\n";

        f << _indent << "  ]";
        if (_include_connections) {
            f << ",\n" << _indent << "  \"connections\": [\n";

            bool first_conn{true};
            for (const auto& conn : mod->connections()) {
                if (!first_conn)
                    f << ",\n";

                write_mod_conn(conn, indent_level + 2);

                first_conn = false;
            }

            f << _indent << "  ]";
        }
        if (_include_attributes) {
            f << ",\n" << _indent << "  \"attributes\": {\n";

            write_prams(mod->attributes, indent_level + 2);

            f << "\n";
            f << _indent << "  }";
        }
        f << "\n" << _indent << "}";
    }

    void write_cell_ports(RTLIL::Cell* port_cell, uint64_t indent_level = 0) {
        const auto _indent = gen_indent(indent_level);

        bool first_port{true};
        for (auto con : port_cell->connections()) {
            if (!first_port)
                f << ",\n";

            f << _indent << "  {\n";
            f << stringf("    %s\"name\": \"%s\",\n", _indent.c_str(), escape_string(RTLIL::unescape_id(con.first)).c_str());
            f << _indent << "    \"direction\": \"";
            if (port_cell->input(con.first))
                f << "i";
            if (port_cell->input(con.first))
                f << "o";
            f << "\",\n";
            if (con.second.size() == 1)
                f << _indent << "    \"range\": [0, 0]\n";
            else
                f << stringf("    %s\"range\": [%d, %d]\n", _indent.c_str(), con.second.size(), 0);
            f << _indent << "  }";

            first_port = false;
        }
        f << "\n";
    }


    void write_cell_sort(std::pair<const std::string, std::vector<Cell*>>& sort, uint16_t indent_level = 0) {
        const auto port_cell = sort.second.front();
        const auto _indent = gen_indent(indent_level);

        f << _indent << "{\n";
        f << stringf("  %s\"type\": \"%s\",\n", _indent.c_str(), sort.first.c_str());
        f << _indent << "  \"ports\": [\n";

        write_cell_ports(port_cell, indent_level + 2);

        f << _indent << "  ],\n" << _indent << "  \"cells\": [\n";

        bool first_cell{true};
        for (auto& cell : sort.second) {
            if (!first_cell)
                f << ",\n";

            write_cell(cell, indent_level + 2);

            first_cell = false;
        }

        f << "\n";
        f << _indent << "  ]\n";
        f << _indent << "}";
    }

    void write_param_val(const Const& v) {
        if ((v.flags & RTLIL::ConstFlags::CONST_FLAG_STRING) == RTLIL::ConstFlags::CONST_FLAG_STRING) {
            const auto str = v.decode_string();

            // XXX(aki): TODO, uh, yeah

            f << "\"" << escape_string(str) << "\"";
        } else if ((v.flags & RTLIL::ConstFlags::CONST_FLAG_SIGNED) == RTLIL::ConstFlags::CONST_FLAG_SIGNED) {
            f << stringf("\"%dsd %d\"", v.size(), v.as_int(true));
        } else if ((v.flags & RTLIL::ConstFlags::CONST_FLAG_REAL) == RTLIL::ConstFlags::CONST_FLAG_REAL) {

        } else {
            f << "\"" << escape_string(v.as_string()) << "\"";
        }
    }

    void write_prams(dict<RTLIL::IdString, RTLIL::Const>& params, uint16_t indent_level = 0) {
        const auto _indent = gen_indent(indent_level);

        bool first_param{true};
        for (auto& param : params) {
            if (!first_param)
                f << stringf(",\n");
            const auto param_val = param.second;
            if (!param_val.empty()) {
                f << stringf("  %s\"%s\": ", _indent.c_str(), escape_string(RTLIL::unescape_id(param.first)).c_str());
                write_param_val(param_val);
            } else {
                f << stringf("  %s\"%s\": true", _indent.c_str(), escape_string(RTLIL::unescape_id(param.first)).c_str());
            }

            first_param = false;
        }
    }

    void write_cell(Cell* cell, uint16_t indent_level = 0) {
        const auto _indent = gen_indent(indent_level);
        log_assert(cell != nullptr);

        f << _indent << "  {\n";
        f << stringf("    %s\"name\": \"%s\"", _indent.c_str(), escape_string(RTLIL::unescape_id(cell->name)).c_str());

        if (_include_connections) {
            f << ",\n" << _indent << "    \"connections\": [\n";

            bool first_conn{true};
            for (const auto& conn : cell->connections()) {
                if (!first_conn)
                    f << ",\n";

                write_cell_conn(conn, indent_level + 2);

                first_conn = false;
            }

            f << "\n";
            f << _indent << "    ]";
        }

        if (_include_attributes) {
            f << ",\n" << _indent << "    \"attributes\": {\n";

            write_prams(cell->attributes, indent_level + 2);

            f << "\n";
            f << _indent << "    }";
        }

        if (_include_properties) {
            f << ",\n" << _indent << "    \"parameters\": {\n";

            write_prams(cell->parameters, indent_level + 2);

            f << "\n";
            f << _indent << "    }";
        }

        f << "\n" << _indent << "  }";
    }
};

struct JnyBackend : public Backend {
    JnyBackend() : Backend("jny", "generate design metadata") { }
    void help() override {
        //   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
        log("\n");
        log("    jny [options] [selection]\n");
        log("\n");
        log("Write JSON netlist metadata for the current design\n");
        log("\n");
        log("    -no-connections\n");
        log("        Don't include connection information in the netlist output.\n");
        log("\n");
        log("    -no-attributes\n");
        log("        Don't include attributed information in the netlist output.\n");
        log("\n");
        log("    -no-properties\n");
        log("        Don't include property information in the netlist output.\n");
        log("\n");
        log("The JSON schema for JNY output files is located in the \"jny.schema.json\" file\n");
        log("which is located at \"https://raw.githubusercontent.com/YosysHQ/yosys/main/misc/jny.schema.json\"\n");
        log("\n");
    }

    void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design) override {

        bool connections{true};
        bool attributes{true};
        bool properties{true};

        size_t argidx{1};
        for (; argidx < args.size(); argidx++) {
            if (args[argidx] == "-no-connections") {
                connections = false;
                continue;
            }

            if (args[argidx] == "-no-attributes") {
                attributes = false;
                continue;
            }

            if (args[argidx] == "-no-properties") {
                properties = false;
                continue;
            }

            break;
        }

        // Compose invocation line
        std::ostringstream invk;
        if (!args.empty()) {
            std::copy(args.begin(), args.end(),
                std::ostream_iterator<std::string>(invk, " ")
            );
        }
        invk << filename;

        extra_args(f, filename, args, argidx);

        log_header(design, "Executing jny backend.\n");

        JnyWriter jny_writer(*f, false, connections, attributes, properties);
        jny_writer.write_metadata(design, 0, invk.str());
    }

} JnyBackend;


struct JnyPass : public Pass {
    JnyPass() : Pass("jny", "write design and metadata") { }

    void help() override {
        //   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
        log("\n");
        log("    jny [options] [selection]\n");
        log("\n");
        log("Write JSON netlist metadata for the current design\n");
        log("\n");
        log("    -o <filename>\n");
        log("        write to the specified file.\n");
        log("\n");
        log("    -no-connections\n");
        log("        Don't include connection information in the netlist output.\n");
        log("\n");
        log("    -no-attributes\n");
        log("        Don't include attributed information in the netlist output.\n");
        log("\n");
        log("    -no-properties\n");
        log("        Don't include property information in the netlist output.\n");
        log("\n");
        log("See 'help write_jny' for a description of the JSON format used.\n");
        log("\n");
    }
    void execute(std::vector<std::string> args, RTLIL::Design *design) override {
        std::string filename{};

        bool connections{true};
        bool attributes{true};
        bool properties{true};

        size_t argidx{1};
        for (; argidx < args.size(); argidx++) {
            if (args[argidx] == "-o" && argidx+1 < args.size()) {
                filename = args[++argidx];
                continue;
            }

            if (args[argidx] == "-no-connections") {
                connections = false;
                continue;
            }

            if (args[argidx] == "-no-attributes") {
                attributes = false;
                continue;
            }

            if (args[argidx] == "-no-properties") {
                properties = false;
                continue;
            }

            break;
        }

        // Compose invocation line
        std::ostringstream invk;
        if (!args.empty()) {
            std::copy(args.begin(), args.end(),
                std::ostream_iterator<std::string>(invk, " ")
            );
        }

        extra_args(args, argidx, design);

        std::ostream *f;
        std::stringstream buf;
        bool empty = filename.empty();

        if (!empty) {
            rewrite_filename(filename);
            std::ofstream *ff = new std::ofstream;
            ff->open(filename.c_str(), std::ofstream::trunc);
            if (ff->fail()) {
                delete ff;
                log_error("Can't open file `%s' for writing: %s\n", filename.c_str(), strerror(errno));
            }
            f = ff;
            invk << filename;
        } else {
            f = &buf;
        }


        JnyWriter jny_writer(*f, false, connections, attributes, properties);
        jny_writer.write_metadata(design, 0, invk.str());

        if (!empty) {
            delete f;
        } else {
            log("%s", buf.str().c_str());
        }
    }

} JnyPass;

PRIVATE_NAMESPACE_END
