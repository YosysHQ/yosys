#include "kernel/register.h"
#include "kernel/celltypes.h"
#include "kernel/log.h"
#include "kernel/sigtools.h"
#include "dot.h"
#include <string>
#include <sstream>
#include <set>
#include <map>

USING_YOSYS_NAMESPACE
using namespace DOT_BACKEND;

using RTLIL::id2cstr;

#undef CLUSTER_CELLS_AND_PORTBOXES

uint32_t ShowWorker::xorshift32(uint32_t x) {
    x ^= x << 13;
    x ^= x >> 17;
    x ^= x << 5;
    return x;
}

std::string ShowWorker::nextColor()
{
    if (currentColor == 0)
        return "color=\"black\"";
    return stringf("colorscheme=\"dark28\", color=\"%d\", fontcolor=\"%d\"", currentColor%8+1, currentColor%8+1);
}

std::string ShowWorker::nextColor(std::string presetColor)
{
    if (presetColor.empty())
        return nextColor();
    return presetColor;
}

std::string ShowWorker::nextColor(RTLIL::SigSpec sig, std::string defaultColor)
{
    sig.sort_and_unify();
    for (auto &c : sig.chunks()) {
        if (c.wire != NULL)
            for (auto &s : color_selections)
                if (s.second.selected_members.count(module->name) > 0 && s.second.selected_members.at(module->name).count(c.wire->name) > 0)
                    return stringf("color=\"%s\"", s.first.c_str());
    }
    return defaultColor;
}

std::string ShowWorker::nextColor(const RTLIL::SigSig &conn, std::string defaultColor)
{
    return nextColor(conn.first, nextColor(conn.second, defaultColor));
}

std::string ShowWorker::nextColor(const RTLIL::SigSpec &sig)
{
    return nextColor(sig, nextColor());
}

std::string ShowWorker::nextColor(const RTLIL::SigSig &conn)
{
    return nextColor(conn, nextColor());
}

std::string ShowWorker::widthLabel(int bits)
{
    if (bits <= 1)
        return "label=\"\"";
    if (!genWidthLabels)
        return "style=\"setlinewidth(3)\", label=\"\"";
    return stringf("style=\"setlinewidth(3)\", label=\"<%d>\"", bits);
}

const char *ShowWorker::findColor(std::string member_name)
{
    for (auto &s : color_selections)
        if (s.second.selected_member(module->name, member_name)) {
            dot_escape_store.push_back(stringf(", color=\"%s\"", s.first.c_str()));
            return dot_escape_store.back().c_str();
        }

    RTLIL::Const colorattr_value;
    RTLIL::Cell *cell = module->cell(member_name);
    RTLIL::Wire *wire = module->wire(member_name);

    if (cell && cell->attributes.count(colorattr))
        colorattr_value = cell->attributes.at(colorattr);
    else if (wire && wire->attributes.count(colorattr))
        colorattr_value = wire->attributes.at(colorattr);
    else
        return "";

    if (colorattr_cache.count(colorattr_value) == 0) {
        int next_id = GetSize(colorattr_cache);
        colorattr_cache[colorattr_value] = (next_id % 8) + 1;
    }

    dot_escape_store.push_back(stringf(", colorscheme=\"dark28\", color=\"%d\", fontcolor=\"%d\"", colorattr_cache.at(colorattr_value), colorattr_cache.at(colorattr_value)));
    return dot_escape_store.back().c_str();
}

const char *ShowWorker::findLabel(std::string member_name)
{
    for (auto &s : label_selections)
        if (s.second.selected_member(module->name, member_name))
            return escape(s.first);
    return escape(member_name, true);
}

const char *ShowWorker::escape(std::string id, bool is_name)
{
    if (id.size() == 0)
        return "";

    if (id[0] == '$' && is_name) {
        if (enumerateIds) {
            if (autonames.count(id) == 0) {
                autonames[id] = autonames.size() + 1;
                log("Generated short name for internal identifier: _%d_ -> %s\n", autonames[id], id.c_str());
            }
            id = stringf("_%d_", autonames[id]);
        } else if (abbreviateIds) {
            const char *p = id.c_str();
            const char *q = strrchr(p, '$');
            id = std::string(q);
        }
    }

    if (id[0] == '\\')
        id = id.substr(1);

    std::string str;
    for (char ch : id) {
        if (ch == '\\' || ch == '"')
            str += "\\";
        str += ch;
    }

    dot_escape_store.push_back(str);
    return dot_escape_store.back().c_str();
}

int ShowWorker::id2num(RTLIL::IdString id)
{
    if (dot_id2num_store.count(id) > 0)
        return dot_id2num_store[id];
    return dot_id2num_store[id] = dot_id2num_store.size() + 1;
}

std::string ShowWorker::gen_signode_simple(RTLIL::SigSpec sig, bool range_check)
{
    if (GetSize(sig) == 0) {
        fprintf(f, "v%d [ label=\"\" ];\n", single_idx_count);
        return stringf("v%d", single_idx_count++);
    }

    if (sig.is_chunk()) {
        const RTLIL::SigChunk &c = sig.as_chunk();
        if (c.wire != NULL && design->selected_member(module->name, c.wire->name)) {
            if (!range_check || c.wire->width == c.width)
                return stringf("n%d", id2num(c.wire->name));
        } else {
            fprintf(f, "v%d [ label=\"%s\" ];\n", single_idx_count, findLabel(log_signal(c)));
            return stringf("v%d", single_idx_count++);
        }
    }

    return std::string();
}

std::string ShowWorker::gen_portbox(std::string port, RTLIL::SigSpec sig, bool driver, std::string *node)
{
    std::string code;
    std::string net = gen_signode_simple(sig);
    if (net.empty())
    {
        std::string label_string;
        int pos = sig.size()-1;
        int idx = single_idx_count++;
        for (int rep, i = int(sig.chunks().size())-1; i >= 0; i -= rep) {
            const RTLIL::SigChunk &c = sig.chunks().at(i);
            net = gen_signode_simple(c, false);
            log_assert(!net.empty());
            for (rep = 1; i-rep >= 0 && c == sig.chunks().at(i-rep); rep++) {}
            std::string repinfo = rep > 1 ? stringf("%dx ", rep) : "";
            if (driver) {
                label_string += stringf("<s%d> %d:%d - %s%d:%d |", i, pos, pos-c.width+1, repinfo.c_str(), c.offset+c.width-1, c.offset);
                net_conn_map[net].in.insert(stringf("x%d:s%d", idx, i));
                net_conn_map[net].bits = rep*c.width;
                net_conn_map[net].color = nextColor(c, net_conn_map[net].color);
            } else {
                label_string += stringf("<s%d> %s%d:%d - %d:%d |", i, repinfo.c_str(), c.offset+c.width-1, c.offset, pos, pos-rep*c.width+1);
                net_conn_map[net].out.insert(stringf("x%d:s%d", idx, i));
                net_conn_map[net].bits = rep*c.width;
                net_conn_map[net].color = nextColor(c, net_conn_map[net].color);
            }
            pos -= rep * c.width;
        }
        if (label_string[label_string.size()-1] == '|')
            label_string = label_string.substr(0, label_string.size()-1);
        code += stringf("x%d [ shape=record, style=rounded, label=\"%s\" ];\n", idx, label_string.c_str());
        if (!port.empty()) {
            currentColor = xorshift32(currentColor);
            if (driver)
                code += stringf("%s:e -> x%d:w [arrowhead=odiamond, arrowtail=odiamond, dir=both, %s, %s];\n", port.c_str(), idx, nextColor(sig).c_str(), widthLabel(sig.size()).c_str());
            else
                code += stringf("x%d:e -> %s:w [arrowhead=odiamond, arrowtail=odiamond, dir=both, %s, %s];\n", idx, port.c_str(), nextColor(sig).c_str(), widthLabel(sig.size()).c_str());
        }
        if (node != NULL)
            *node = stringf("x%d", idx);
    }
    else
    {
        if (!port.empty()) {
            if (driver)
                net_conn_map[net].in.insert(port);
            else
                net_conn_map[net].out.insert(port);
            net_conn_map[net].bits = sig.size();
            net_conn_map[net].color = nextColor(sig, net_conn_map[net].color);
        }
        if (node != NULL)
            *node = net;
    }
    return code;
}

void ShowWorker::collect_proc_signals(std::vector<RTLIL::SigSpec> &obj, std::set<RTLIL::SigSpec> &signals)
{
    for (auto &it : obj)
        if (!it.is_fully_const())
            signals.insert(it);
}

void ShowWorker::collect_proc_signals(std::vector<RTLIL::SigSig> &obj, std::set<RTLIL::SigSpec> &input_signals, std::set<RTLIL::SigSpec> &output_signals)
{
    for (auto &it : obj) {
        output_signals.insert(it.first);
        if (!it.second.is_fully_const())
            input_signals.insert(it.second);
    }
}

void ShowWorker::collect_proc_signals(RTLIL::CaseRule *obj, std::set<RTLIL::SigSpec> &input_signals, std::set<RTLIL::SigSpec> &output_signals)
{
    collect_proc_signals(obj->compare, input_signals);
    collect_proc_signals(obj->actions, input_signals, output_signals);
    for (auto it : obj->switches)
        collect_proc_signals(it, input_signals, output_signals);
}

void ShowWorker::collect_proc_signals(RTLIL::SwitchRule *obj, std::set<RTLIL::SigSpec> &input_signals, std::set<RTLIL::SigSpec> &output_signals)
{
    input_signals.insert(obj->signal);
    for (auto it : obj->cases)
        collect_proc_signals(it, input_signals, output_signals);
}

void ShowWorker::collect_proc_signals(RTLIL::SyncRule *obj, std::set<RTLIL::SigSpec> &input_signals, std::set<RTLIL::SigSpec> &output_signals)
{
    input_signals.insert(obj->signal);
    collect_proc_signals(obj->actions, input_signals, output_signals);
}

void ShowWorker::collect_proc_signals(RTLIL::Process *obj, std::set<RTLIL::SigSpec> &input_signals, std::set<RTLIL::SigSpec> &output_signals)
{
    collect_proc_signals(&obj->root_case, input_signals, output_signals);
    for (auto it : obj->syncs)
        collect_proc_signals(it, input_signals, output_signals);
}

void ShowWorker::handle_module()
{
    single_idx_count = 0;
    dot_escape_store.clear();
    dot_id2num_store.clear();
    net_conn_map.clear();

    fprintf(f, "digraph \"%s\" {\n", escape(module->name.str()));
    if (!notitle)
        fprintf(f, "label=\"%s\";\n", escape(module->name.str()));
    fprintf(f, "rankdir=\"LR\";\n");
    fprintf(f, "remincross=true;\n");

    std::set<std::string> all_sources, all_sinks;

    std::map<std::string, std::string> wires_on_demand;
    for (auto &it : module->wires_) {
        if (!design->selected_member(module->name, it.first))
            continue;
        const char *shape = "diamond";
        if (it.second->port_input || it.second->port_output)
            shape = "octagon";
        if (it.first[0] == '\\') {
            fprintf(f, "n%d [ shape=%s, label=\"%s\", %s, fontcolor=\"black\" ];\n",
                    id2num(it.first), shape, findLabel(it.first.str()),
                    nextColor(RTLIL::SigSpec(it.second), "color=\"black\"").c_str());
            if (it.second->port_input)
                all_sources.insert(stringf("n%d", id2num(it.first)));
            else if (it.second->port_output)
                all_sinks.insert(stringf("n%d", id2num(it.first)));
        } else {
            wires_on_demand[stringf("n%d", id2num(it.first))] = it.first.str();
        }
    }

    if (stretchIO)
    {
        fprintf(f, "{ rank=\"source\";");
        for (auto n : all_sources)
            fprintf(f, " %s;", n.c_str());
        fprintf(f, "}\n");

        fprintf(f, "{ rank=\"sink\";");
        for (auto n : all_sinks)
            fprintf(f, " %s;", n.c_str());
        fprintf(f, "}\n");
    }

    for (auto &it : module->cells_)
    {
        if (!design->selected_member(module->name, it.first))
            continue;

        std::vector<RTLIL::IdString> in_ports, out_ports;

        for (auto &conn : it.second->connections()) {
            if (!ct.cell_output(it.second->type, conn.first))
                in_ports.push_back(conn.first);
            else
                out_ports.push_back(conn.first);
        }

        std::sort(in_ports.begin(), in_ports.end(), RTLIL::sort_by_id_str());
        std::sort(out_ports.begin(), out_ports.end(), RTLIL::sort_by_id_str());

        std::string label_string = "{{";

        for (auto &p : in_ports)
            label_string += stringf("<p%d> %s%s|", id2num(p), escape(p.str()),
                                    genSignedLabels && it.second->hasParam(p.str() + "_SIGNED") &&
                                    it.second->getParam(p.str() + "_SIGNED").as_bool() ? "*" : "");
        if (label_string[label_string.size()-1] == '|')
            label_string = label_string.substr(0, label_string.size()-1);

        label_string += stringf("}|%s\\n%s|{", findLabel(it.first.str()), escape(it.second->type.str()));

        for (auto &p : out_ports)
            label_string += stringf("<p%d> %s|", id2num(p), escape(p.str()));
        if (label_string[label_string.size()-1] == '|')
            label_string = label_string.substr(0, label_string.size()-1);

        label_string += "}}";

        std::string code;
        for (auto &conn : it.second->connections()) {
            code += gen_portbox(stringf("c%d:p%d", id2num(it.first), id2num(conn.first)),
                                conn.second, ct.cell_output(it.second->type, conn.first));
        }

#ifdef CLUSTER_CELLS_AND_PORTBOXES
        if (!code.empty())
            fprintf(f, "subgraph cluster_c%d {\nc%d [ shape=record, label=\"%s\"%s ];\n%s}\n",
                    id2num(it.first), id2num(it.first), label_string.c_str(), findColor(it.first), code.c_str());
        else
#endif
            fprintf(f, "c%d [ shape=record, label=\"%s\"%s ];\n%s",
                    id2num(it.first), label_string.c_str(), findColor(it.first.str()), code.c_str());
    }

    for (auto &it : module->processes)
    {
        RTLIL::Process *proc = it.second;

        if (!design->selected_member(module->name, proc->name))
            continue;

        std::set<RTLIL::SigSpec> input_signals, output_signals;
        collect_proc_signals(proc, input_signals, output_signals);

        int pidx = single_idx_count++;
        input_signals.erase(RTLIL::SigSpec());
        output_signals.erase(RTLIL::SigSpec());

        for (auto &sig : input_signals) {
            std::string code, node;
            code += gen_portbox("", sig, false, &node);
            fprintf(f, "%s", code.c_str());
            net_conn_map[node].out.insert(stringf("p%d", pidx));
            net_conn_map[node].bits = sig.size();
            net_conn_map[node].color = nextColor(sig, net_conn_map[node].color);
        }

        for (auto &sig : output_signals) {
            std::string code, node;
            code += gen_portbox("", sig, true, &node);
            fprintf(f, "%s", code.c_str());
            net_conn_map[node].in.insert(stringf("p%d", pidx));
            net_conn_map[node].bits = sig.size();
            net_conn_map[node].color = nextColor(sig, net_conn_map[node].color);
        }

        std::string proc_src = RTLIL::unescape_id(proc->name);
        if (proc->attributes.count("\\src") > 0)
            proc_src = proc->attributes.at("\\src").decode_string();
        fprintf(f, "p%d [shape=box, style=rounded, label=\"PROC %s\\n%s\"];\n", pidx, findLabel(proc->name.str()), proc_src.c_str());
    }

    for (auto &conn : module->connections())
    {
        bool found_lhs_wire = false;
        for (auto &c : conn.first.chunks()) {
            if (c.wire == NULL || design->selected_member(module->name, c.wire->name))
                found_lhs_wire = true;
        }
        bool found_rhs_wire = false;
        for (auto &c : conn.second.chunks()) {
            if (c.wire == NULL || design->selected_member(module->name, c.wire->name))
                found_rhs_wire = true;
        }
        if (!found_lhs_wire || !found_rhs_wire)
            continue;

        std::string code, left_node, right_node;
        code += gen_portbox("", conn.second, false, &left_node);
        code += gen_portbox("", conn.first, true, &right_node);
        fprintf(f, "%s", code.c_str());

        if (left_node[0] == 'x' && right_node[0] == 'x') {
            currentColor = xorshift32(currentColor);
            fprintf(f, "%s:e -> %s:w [arrowhead=odiamond, arrowtail=odiamond, dir=both, %s, %s];\n", left_node.c_str(), right_node.c_str(), nextColor(conn).c_str(), widthLabel(conn.first.size()).c_str());
        } else {
            net_conn_map[right_node].bits = conn.first.size();
            net_conn_map[right_node].color = nextColor(conn, net_conn_map[right_node].color);
            net_conn_map[left_node].bits = conn.first.size();
            net_conn_map[left_node].color = nextColor(conn, net_conn_map[left_node].color);
            if (left_node[0] == 'x') {
                net_conn_map[right_node].in.insert(left_node);
            } else if (right_node[0] == 'x') {
                net_conn_map[left_node].out.insert(right_node);
            } else {
                net_conn_map[right_node].in.insert(stringf("x%d:e", single_idx_count));
                net_conn_map[left_node].out.insert(stringf("x%d:w", single_idx_count));
                fprintf(f, "x%d [shape=box, style=rounded, label=\"BUF\"];\n", single_idx_count++);
            }
        }
    }

    for (auto &it : net_conn_map)
    {
        currentColor = xorshift32(currentColor);
        if (wires_on_demand.count(it.first) > 0) {
            if (it.second.in.size() == 1 && it.second.out.size() > 1 && it.second.in.begin()->substr(0, 1) == "p")
                it.second.out.erase(*it.second.in.begin());
            if (it.second.in.size() == 1 && it.second.out.size() == 1) {
                std::string from = *it.second.in.begin(), to = *it.second.out.begin();
                if (from != to || from.substr(0, 1) != "p")
                    fprintf(f, "%s:e -> %s:w [%s, %s];\n", from.c_str(), to.c_str(), nextColor(it.second.color).c_str(), widthLabel(it.second.bits).c_str());
                continue;
            }
            if (it.second.in.size() == 0 || it.second.out.size() == 0)
                fprintf(f, "%s [ shape=diamond, label=\"%s\" ];\n", it.first.c_str(), findLabel(wires_on_demand[it.first]));
            else
                fprintf(f, "%s [ shape=point ];\n", it.first.c_str());
        }
        for (auto &it2 : it.second.in)
            fprintf(f, "%s:e -> %s:w [%s, %s];\n", it2.c_str(), it.first.c_str(), nextColor(it.second.color).c_str(), widthLabel(it.second.bits).c_str());
        for (auto &it2 : it.second.out)
            fprintf(f, "%s:e -> %s:w [%s, %s];\n", it.first.c_str(), it2.c_str(), nextColor(it.second.color).c_str(), widthLabel(it.second.bits).c_str());
    }

    fprintf(f, "}\n");
}

/* TODO: enable usage of iostreams */
// ShowWorker(std::ostream *s, RTLIL::Design *design,) : f(NULL), s {}


ShowWorker::ShowWorker(FILE *f, RTLIL::Design *design, std::vector<RTLIL::Design*> &libs, uint32_t colorSeed, bool genWidthLabels,
                       bool genSignedLabels, bool stretchIO, bool enumerateIds, bool abbreviateIds, bool notitle,
                       const std::vector<std::pair<std::string, RTLIL::Selection>> &color_selections,
                       const std::vector<std::pair<std::string, RTLIL::Selection>> &label_selections, RTLIL::IdString colorattr) :
    f(f), design(design), currentColor(colorSeed), genWidthLabels(genWidthLabels),
    genSignedLabels(genSignedLabels), stretchIO(stretchIO), enumerateIds(enumerateIds), abbreviateIds(abbreviateIds),
    notitle(notitle), color_selections(color_selections), label_selections(label_selections), colorattr(colorattr)
{
    ct.setup_internals();
    ct.setup_internals_mem();
    ct.setup_stdcells();
    ct.setup_stdcells_mem();
    ct.setup_design(design);

    for (auto lib : libs)
        ct.setup_design(lib);

    design->optimize();
    page_counter = 0;
    for (auto &mod_it : design->modules_)
    {
        module = mod_it.second;
        if (!design->selected_module(module->name))
            continue;
        if (design->selected_whole_module(module->name)) {
            if (module->get_bool_attribute("\\blackbox")) {
                // log("Skipping blackbox module %s.\n", id2cstr(module->name));
                continue;
            } else
                if (module->cells_.empty() && module->connections().empty() && module->processes.empty()) {
                    log("Skipping empty module %s.\n", id2cstr(module->name));
                    continue;
                } else
                    log("Dumping module %s to page %d.\n", id2cstr(module->name), ++page_counter);
        } else
            log("Dumping selected parts of module %s to page %d.\n", id2cstr(module->name), ++page_counter);
        handle_module();
    }
}
