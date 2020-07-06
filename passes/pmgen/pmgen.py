#!/usr/bin/env python3

import re
import sys
import pprint
import getopt

pp = pprint.PrettyPrinter(indent=4)

prefix = None
pmgfiles = list()
outfile = None
debug = False
genhdr = False

opts, args = getopt.getopt(sys.argv[1:], "p:o:dg")

for o, a in opts:
    if o == "-p":
        prefix = a
    elif o == "-o":
        outfile = a
    elif o == "-d":
        debug = True
    elif o == "-g":
        genhdr = True

if outfile is None:
    outfile = "/dev/stdout"

for a in args:
    assert a.endswith(".pmg")
    if prefix is None and len(args) == 1:
        prefix = a[0:-4]
        prefix = prefix.split('/')[-1]
    pmgfiles.append(a)

assert prefix is not None

current_pattern = None
current_subpattern = None
patterns = dict()
subpatterns = dict()
subpattern_args = dict()
state_types = dict()
udata_types = dict()
blocks = list()
ids = dict()

def rewrite_cpp(s):
    t = list()
    i = 0
    while i < len(s):
        if s[i] in ("'", '"') and i + 1 < len(s):
            j = i + 1
            while j + 1 < len(s) and s[j] != s[i]:
                if s[j] == '\\' and j + 1 < len(s):
                    j += 1
                j += 1
            t.append(s[i:j+1])
            i = j + 1
            continue

        if s[i] in ('$', '\\') and i + 1 < len(s):
            j = i + 1
            while True:
                if j == len(s):
                    j -= 1
                    break
                if ord('a') <= ord(s[j]) <= ord('z'):
                    j += 1
                    continue
                if ord('A') <= ord(s[j]) <= ord('Z'):
                    j += 1
                    continue
                if ord('0') <= ord(s[j]) <= ord('9'):
                    j += 1
                    continue
                if s[j] == '_':
                    j += 1
                    continue
                j -= 1
                break

            n = s[i:j+1]
            i = j + 1

            if n[0] == '$':
                v = "id_d_" + n[1:]
            else:
                v = "id_b_" + n[1:]

            if v not in ids:
                ids[v] = n
            else:
                assert ids[v] == n

            t.append(v)
            continue

        if s[i] == "\t":
            t.append("  ")
        else:
            t.append(s[i])

        i += 1

    return "".join(t)

def process_pmgfile(f, filename):
    linenr = 0
    global current_pattern
    global current_subpattern
    while True:
        linenr += 1
        line = f.readline()
        if line == "": break
        line = line.strip()

        cmd = line.split()
        if len(cmd) == 0 or cmd[0].startswith("//"): continue
        cmd = cmd[0]

        if cmd == "pattern":
            if current_pattern is not None:
                block = dict()
                block["type"] = "final"
                block["pattern"] = (current_pattern, current_subpattern)
                blocks.append(block)
            line = line.split()
            assert len(line) == 2
            assert line[1] not in patterns
            current_pattern = line[1]
            current_subpattern = ""
            patterns[current_pattern] = len(blocks)
            subpatterns[(current_pattern, current_subpattern)] = len(blocks)
            subpattern_args[(current_pattern, current_subpattern)] = list()
            state_types[current_pattern] = dict()
            udata_types[current_pattern] = dict()
            continue

        assert current_pattern is not None

        if cmd == "fallthrough":
            block = dict()
            block["type"] = "fallthrough"
            blocks.append(block)
            line = line.split()
            assert len(line) == 1
            continue

        if cmd == "subpattern":
            if len(blocks) == 0 or blocks[-1]["type"] != "fallthrough":
                block = dict()
                block["type"] = "final"
                block["pattern"] = (current_pattern, current_subpattern)
                blocks.append(block)
            elif len(blocks) and blocks[-1]["type"] == "fallthrough":
                del blocks[-1]
            line = line.split()
            assert len(line) == 2
            current_subpattern = line[1]
            subpattern_args[(current_pattern, current_subpattern)] = list()
            assert (current_pattern, current_subpattern) not in subpatterns
            subpatterns[(current_pattern, current_subpattern)] = len(blocks)
            continue

        if cmd == "arg":
            line = line.split()
            assert len(line) > 1
            subpattern_args[(current_pattern, current_subpattern)] += line[1:]
            continue

        if cmd == "state":
            m = re.match(r"^state\s+<(.*?)>\s+(([A-Za-z_][A-Za-z_0-9]*\s+)*[A-Za-z_][A-Za-z_0-9]*)\s*$", line)
            assert m
            type_str = m.group(1)
            states_str = m.group(2)
            for s in re.split(r"\s+", states_str):
                assert s not in state_types[current_pattern]
                state_types[current_pattern][s] = type_str
            continue

        if cmd == "udata":
            m = re.match(r"^udata\s+<(.*?)>\s+(([A-Za-z_][A-Za-z_0-9]*\s+)*[A-Za-z_][A-Za-z_0-9]*)\s*$", line)
            assert m
            type_str = m.group(1)
            udatas_str = m.group(2)
            for s in re.split(r"\s+", udatas_str):
                assert s not in udata_types[current_pattern]
                udata_types[current_pattern][s] = type_str
            continue

        if cmd == "match":
            block = dict()
            block["type"] = "match"
            block["src"] = "%s:%d" % (filename, linenr)
            block["pattern"] = (current_pattern, current_subpattern)

            block["genargs"] = None
            block["gencode"] = None

            line = line.split()
            assert len(line) == 2
            assert (line[1] not in state_types[current_pattern]) or (state_types[current_pattern][line[1]] == "Cell*")
            block["cell"] = line[1]
            state_types[current_pattern][line[1]] = "Cell*";

            block["if"] = list()
            block["setup"] = list()
            block["index"] = list()
            block["filter"] = list()
            block["sets"] = list()
            block["optional"] = False
            block["semioptional"] = False

            while True:
                linenr += 1
                l = f.readline()
                assert l != ""
                a = l.split()
                if len(a) == 0 or a[0].startswith("//"): continue
                if a[0] == "endmatch": break

                if a[0] == "if":
                    b = l.lstrip()[2:]
                    block["if"].append(rewrite_cpp(b.strip()))
                    continue

                if a[0] == "select":
                    b = l.lstrip()[6:]
                    block["setup"].append(("select", rewrite_cpp(b.strip())))
                    continue

                if a[0] == "slice":
                    m = re.match(r"^\s*slice\s+(\S+)\s+(.*?)\s*$", l)
                    block["setup"].append(("slice", m.group(1), rewrite_cpp(m.group(2))))
                    continue

                if a[0] == "choice":
                    m = re.match(r"^\s*choice\s+<(.*?)>\s+(\S+)\s+(.*?)\s*$", l)
                    block["setup"].append(("choice", m.group(1), m.group(2), rewrite_cpp(m.group(3))))
                    continue

                if a[0] == "define":
                    m = re.match(r"^\s*define\s+<(.*?)>\s+(\S+)\s+(.*?)\s*$", l)
                    block["setup"].append(("define", m.group(1), m.group(2), rewrite_cpp(m.group(3))))
                    continue

                if a[0] == "index":
                    m = re.match(r"^\s*index\s+<(.*?)>\s+(.*?)\s*===\s*(.*?)\s*$", l)
                    assert m
                    block["index"].append((m.group(1), rewrite_cpp(m.group(2)), rewrite_cpp(m.group(3))))
                    continue

                if a[0] == "filter":
                    b = l.lstrip()[6:]
                    block["filter"].append(rewrite_cpp(b.strip()))
                    continue

                if a[0] == "set":
                    m = re.match(r"^\s*set\s+(\S+)\s+(.*?)\s*$", l)
                    block["sets"].append((m.group(1), rewrite_cpp(m.group(2))))
                    continue

                if a[0] == "optional":
                    block["optional"] = True
                    continue

                if a[0] == "semioptional":
                    block["semioptional"] = True
                    continue

                if a[0] == "generate":
                    block["genargs"] = list([int(s) for s in a[1:]])
                    if len(block["genargs"]) == 0: block["genargs"].append(100)
                    if len(block["genargs"]) == 1: block["genargs"].append(0)
                    assert len(block["genargs"]) == 2
                    block["gencode"] = list()
                    while True:
                        linenr += 1
                        l = f.readline()
                        assert l != ""
                        a = l.split()
                        if len(a) == 1 and a[0] == "endmatch": break
                        block["gencode"].append(rewrite_cpp(l.rstrip()))
                    break

                raise RuntimeError("'%s' statement not recognised on line %d" % (a[0], linenr))

            if block["optional"]:
                assert not block["semioptional"]

            blocks.append(block)
            continue

        if cmd == "code":
            block = dict()
            block["type"] = "code"
            block["src"] = "%s:%d" % (filename, linenr)
            block["pattern"] = (current_pattern, current_subpattern)

            block["code"] = list()
            block["fcode"] = list()
            block["states"] = set()

            for s in line.split()[1:]:
                if s not in state_types[current_pattern]:
                    raise RuntimeError("'%s' not in state_types" % s)
                block["states"].add(s)

            codetype = "code"

            while True:
                linenr += 1
                l = f.readline()
                assert l != ""
                a = l.split()
                if len(a) == 0: continue
                if a[0] == "endcode": break

                if a[0] == "finally":
                    codetype = "fcode"
                    continue

                block[codetype].append(rewrite_cpp(l.rstrip()))

            blocks.append(block)
            continue

        raise RuntimeError("'%s' command not recognised" % cmd)

for fn in pmgfiles:
    with open(fn, "r") as f:
        process_pmgfile(f, fn)

if current_pattern is not None:
    block = dict()
    block["type"] = "final"
    block["pattern"] = (current_pattern, current_subpattern)
    blocks.append(block)

current_pattern = None
current_subpattern = None

if debug:
    pp.pprint(blocks)

with open(outfile, "w") as f:
    for fn in pmgfiles:
        print("// Generated by pmgen.py from {}".format(fn), file=f)
    print("", file=f)

    if genhdr:
        print("#include \"kernel/yosys.h\"", file=f)
        print("#include \"kernel/sigtools.h\"", file=f)
        print("", file=f)
        print("YOSYS_NAMESPACE_BEGIN", file=f)
        print("", file=f)

    print("struct {}_pm {{".format(prefix), file=f)
    print("  Module *module;", file=f)
    print("  SigMap sigmap;", file=f)
    print("  std::function<void()> on_accept;", file=f)
    print("  bool setup_done;", file=f)
    print("  bool generate_mode;", file=f)
    print("  int accept_cnt;", file=f)
    print("", file=f)

    print("  uint32_t rngseed;", file=f)
    print("  int rng(unsigned int n) {", file=f)
    print("    rngseed ^= rngseed << 13;", file=f)
    print("    rngseed ^= rngseed >> 17;", file=f)
    print("    rngseed ^= rngseed << 5;", file=f)
    print("    return rngseed % n;", file=f)
    print("  }", file=f)
    print("", file=f)

    for index in range(len(blocks)):
        block = blocks[index]
        if block["type"] == "match":
            index_types = list()
            for entry in block["index"]:
                index_types.append(entry[0])
            value_types = ["Cell*"]
            for entry in block["setup"]:
                if entry[0] == "slice":
                    value_types.append("int")
                if entry[0] == "choice":
                    value_types.append(entry[1])
                if entry[0] == "define":
                    value_types.append(entry[1])
            print("  typedef std::tuple<{}> index_{}_key_type;".format(", ".join(index_types), index), file=f)
            print("  typedef std::tuple<{}> index_{}_value_type;".format(", ".join(value_types), index), file=f)
            print("  dict<index_{}_key_type, vector<index_{}_value_type>> index_{};".format(index, index, index), file=f)
    print("  dict<SigBit, pool<Cell*>> sigusers;", file=f)
    print("  pool<Cell*> blacklist_cells;", file=f)
    print("  pool<Cell*> autoremove_cells;", file=f)
    print("  dict<Cell*,int> rollback_cache;", file=f)
    print("  int rollback;", file=f)
    print("", file=f)

    for current_pattern in sorted(patterns.keys()):
        print("  struct state_{}_t {{".format(current_pattern), file=f)
        for s, t in sorted(state_types[current_pattern].items()):
            print("    {} {};".format(t, s), file=f)
        print("  }} st_{};".format(current_pattern), file=f)
        print("", file=f)

        print("  struct udata_{}_t {{".format(current_pattern), file=f)
        for s, t in sorted(udata_types[current_pattern].items()):
            print("    {} {};".format(t, s), file=f)
        print("  }} ud_{};".format(current_pattern), file=f)
        print("", file=f)
    current_pattern = None

    for v, n in sorted(ids.items()):
        if n[0] == "\\":
            print("  IdString {}{{\"\\{}\"}};".format(v, n), file=f)
        else:
            print("  IdString {}{{\"{}\"}};".format(v, n), file=f)
    print("", file=f)

    print("  void add_siguser(const SigSpec &sig, Cell *cell) {", file=f)
    print("    for (auto bit : sigmap(sig)) {", file=f)
    print("      if (bit.wire == nullptr) continue;", file=f)
    print("      sigusers[bit].insert(cell);", file=f)
    print("    }", file=f)
    print("  }", file=f)
    print("", file=f)

    print("  void blacklist(Cell *cell) {", file=f)
    print("    if (cell != nullptr && blacklist_cells.insert(cell).second) {", file=f)
    print("      auto ptr = rollback_cache.find(cell);", file=f)
    print("      if (ptr == rollback_cache.end()) return;", file=f)
    print("      int rb = ptr->second;", file=f)
    print("      if (rollback == 0 || rollback > rb)", file=f)
    print("        rollback = rb;", file=f)
    print("    }", file=f)
    print("  }", file=f)
    print("", file=f)

    print("  void autoremove(Cell *cell) {", file=f)
    print("    if (cell != nullptr) {", file=f)
    print("      autoremove_cells.insert(cell);", file=f)
    print("      blacklist(cell);", file=f)
    print("    }", file=f)
    print("  }", file=f)
    print("", file=f)

    current_pattern = None

    print("  SigSpec port(Cell *cell, IdString portname) {", file=f)
    print("    return sigmap(cell->getPort(portname));", file=f)
    print("  }", file=f)
    print("", file=f)
    print("  SigSpec port(Cell *cell, IdString portname, const SigSpec& defval) {", file=f)
    print("    return sigmap(cell->connections_.at(portname, defval));", file=f)
    print("  }", file=f)
    print("", file=f)

    print("  Const param(Cell *cell, IdString paramname) {", file=f)
    print("    return cell->getParam(paramname);", file=f)
    print("  }", file=f)
    print("", file=f)
    print("  Const param(Cell *cell, IdString paramname, const Const& defval) {", file=f)
    print("    return cell->parameters.at(paramname, defval);", file=f)
    print("  }", file=f)
    print("", file=f)

    print("  int nusers(const SigSpec &sig) {", file=f)
    print("    pool<Cell*> users;", file=f)
    print("    for (auto bit : sigmap(sig))", file=f)
    print("      for (auto user : sigusers[bit])", file=f)
    print("        users.insert(user);", file=f)
    print("    return GetSize(users);", file=f)
    print("  }", file=f)
    print("", file=f)

    print("  {}_pm(Module *module, const vector<Cell*> &cells) :".format(prefix), file=f)
    print("      module(module), sigmap(module), setup_done(false), generate_mode(false), rngseed(12345678) {", file=f)
    print("    setup(cells);", file=f)
    print("  }", file=f)
    print("", file=f)

    print("  {}_pm(Module *module) :".format(prefix), file=f)
    print("      module(module), sigmap(module), setup_done(false), generate_mode(false), rngseed(12345678) {", file=f)
    print("  }", file=f)
    print("", file=f)

    print("  void setup(const vector<Cell*> &cells) {", file=f)
    for current_pattern in sorted(patterns.keys()):
        for s, t in sorted(udata_types[current_pattern].items()):
            if t.endswith("*"):
                print("    ud_{}.{} = nullptr;".format(current_pattern,s), file=f)
            else:
                print("    ud_{}.{} = {}();".format(current_pattern, s, t), file=f)
    current_pattern = None
    print("    log_assert(!setup_done);", file=f)
    print("    setup_done = true;", file=f)
    print("    for (auto port : module->ports)", file=f)
    print("      add_siguser(module->wire(port), nullptr);", file=f)
    print("    for (auto cell : module->cells())", file=f)
    print("      for (auto &conn : cell->connections())", file=f)
    print("        add_siguser(conn.second, cell);", file=f)
    print("    for (auto cell : cells) {", file=f)

    for index in range(len(blocks)):
        block = blocks[index]
        if block["type"] == "match":
            print("      do {", file=f)
            print("        Cell *{} = cell;".format(block["cell"]), file=f)
            print("        index_{}_value_type value;".format(index), file=f)
            print("        std::get<0>(value) = cell;", file=f)
            loopcnt = 0
            valueidx = 1
            for item in block["setup"]:
                if item[0] == "select":
                    print("        if (!({})) continue;".format(item[1]), file=f)
                if item[0] == "slice":
                    print("        int &{} = std::get<{}>(value);".format(item[1], valueidx), file=f)
                    print("        for ({} = 0; {} < {}; {}++) {{".format(item[1], item[1], item[2], item[1]), file=f)
                    valueidx += 1
                    loopcnt += 1
                if item[0] == "choice":
                    print("        vector<{}> _pmg_choices_{} = {};".format(item[1], item[2], item[3]), file=f)
                    print("        for (const {} &{} : _pmg_choices_{}) {{".format(item[1], item[2], item[2]), file=f)
                    print("        std::get<{}>(value) = {};".format(valueidx, item[2]), file=f)
                    valueidx += 1
                    loopcnt += 1
                if item[0] == "define":
                    print("        {} &{} = std::get<{}>(value);".format(item[1], item[2], valueidx), file=f)
                    print("        {} = {};".format(item[2], item[3]), file=f)
                    valueidx += 1
            print("        index_{}_key_type key;".format(index), file=f)
            for field, entry in enumerate(block["index"]):
                print("        std::get<{}>(key) = {};".format(field, entry[1]), file=f)
            print("        index_{}[key].push_back(value);".format(index), file=f)
            for i in range(loopcnt):
                print("        }", file=f)
            print("      } while (0);", file=f)

    print("    }", file=f)
    print("  }", file=f)
    print("", file=f)

    print("  ~{}_pm() {{".format(prefix), file=f)
    print("    for (auto cell : autoremove_cells)", file=f)
    print("      module->remove(cell);", file=f)
    print("  }", file=f)
    print("", file=f)

    for current_pattern in sorted(patterns.keys()):
        print("  int run_{}(std::function<void()> on_accept_f) {{".format(current_pattern), file=f)
        print("    log_assert(setup_done);", file=f)
        print("    accept_cnt = 0;", file=f)
        print("    on_accept = on_accept_f;", file=f)
        print("    rollback = 0;", file=f)
        for s, t in sorted(state_types[current_pattern].items()):
            if t.endswith("*"):
                print("    st_{}.{} = nullptr;".format(current_pattern, s), file=f)
            else:
                print("    st_{}.{} = {}();".format(current_pattern, s, t), file=f)
        print("    block_{}(1);".format(patterns[current_pattern]), file=f)
        print("    log_assert(rollback_cache.empty());", file=f)
        print("    return accept_cnt;", file=f)
        print("  }", file=f)
        print("", file=f)
        print("  int run_{}(std::function<void({}_pm&)> on_accept_f) {{".format(current_pattern, prefix), file=f)
        print("    return run_{}([&](){{on_accept_f(*this);}});".format(current_pattern), file=f)
        print("  }", file=f)
        print("", file=f)
        print("  int run_{}() {{".format(current_pattern), file=f)
        print("    return run_{}([](){{}});".format(current_pattern, current_pattern), file=f)
        print("  }", file=f)
        print("", file=f)

    if len(subpatterns):
        for p, s in sorted(subpatterns.keys()):
            print("  void block_subpattern_{}_{}(int recursion) {{ block_{}(recursion); }}".format(p, s, subpatterns[(p, s)]), file=f)
        print("", file=f)

    current_pattern = None
    current_subpattern = None

    for index in range(len(blocks)):
        block = blocks[index]

        if block["type"] in ("match", "code"):
            print("  // {}".format(block["src"]), file=f)

        print("  void block_{}(int recursion YS_ATTRIBUTE(unused)) {{".format(index), file=f)
        current_pattern, current_subpattern = block["pattern"]

        if block["type"] == "final":
            print("  }", file=f)
            if index+1 != len(blocks):
                print("", file=f)
            continue

        const_st = set()
        nonconst_st = set()
        restore_st = set()

        for s in subpattern_args[(current_pattern, current_subpattern)]:
            const_st.add(s)

        for i in range(subpatterns[(current_pattern, current_subpattern)], index):
            if blocks[i]["type"] == "code":
                for s in blocks[i]["states"]:
                    const_st.add(s)
            elif blocks[i]["type"] == "match":
                const_st.add(blocks[i]["cell"])
                for item in blocks[i]["sets"]:
                    const_st.add(item[0])
            else:
                assert False

        if block["type"] == "code":
            for s in block["states"]:
                if s in const_st:
                    const_st.remove(s)
                    restore_st.add(s)
                nonconst_st.add(s)
        elif block["type"] == "match":
            s = block["cell"]
            assert s not in const_st
            nonconst_st.add(s)
            for item in block["sets"]:
                if item[0] in const_st:
                    const_st.remove(item[0])
                nonconst_st.add(item[0])
        else:
            assert False

        for s in sorted(const_st):
            t = state_types[current_pattern][s]
            if t.endswith("*"):
                print("    {} const &{} YS_ATTRIBUTE(unused) = st_{}.{};".format(t, s, current_pattern, s), file=f)
            else:
                print("    const {} &{} YS_ATTRIBUTE(unused) = st_{}.{};".format(t, s, current_pattern, s), file=f)

        for s in sorted(nonconst_st):
            t = state_types[current_pattern][s]
            print("    {} &{} YS_ATTRIBUTE(unused) = st_{}.{};".format(t, s, current_pattern, s), file=f)

        for u in sorted(udata_types[current_pattern].keys()):
            t = udata_types[current_pattern][u]
            print("    {} &{} YS_ATTRIBUTE(unused) = ud_{}.{};".format(t, u, current_pattern, u), file=f)

        if len(restore_st):
            print("", file=f)
            for s in sorted(restore_st):
                t = state_types[current_pattern][s]
                print("    {} _pmg_backup_{} = {};".format(t, s, s), file=f)

        if block["type"] == "code":
            print("", file=f)
            print("#define reject do { goto rollback_label; } while(0)", file=f)
            print("#define accept do { accept_cnt++; on_accept(); if (rollback) goto rollback_label; } while(0)", file=f)
            print("#define finish do { rollback = -1; goto rollback_label; } while(0)", file=f)
            print("#define branch do {{ block_{}(recursion+1); if (rollback) goto rollback_label; }} while(0)".format(index+1), file=f)
            print("#define subpattern(pattern_name) do {{ block_subpattern_{}_ ## pattern_name (recursion+1); if (rollback) goto rollback_label; }} while(0)".format(current_pattern), file=f)

            for line in block["code"]:
                print("  " + line, file=f)

            print("", file=f)
            print("    block_{}(recursion+1);".format(index+1), file=f)

            print("#undef reject", file=f)
            print("#undef accept", file=f)
            print("#undef finish", file=f)
            print("#undef branch", file=f)
            print("#undef subpattern", file=f)

            print("", file=f)
            print("rollback_label:", file=f)
            print("    YS_ATTRIBUTE(unused);", file=f)

            if len(block["fcode"]):
                print("#define accept do { accept_cnt++; on_accept(); } while(0)", file=f)
                print("#define finish do { rollback = -1; goto finish_label; } while(0)", file=f)
                for line in block["fcode"]:
                    print("  " + line, file=f)
                print("finish_label:", file=f)
                print("    YS_ATTRIBUTE(unused);", file=f)
                print("#undef accept", file=f)
                print("#undef finish", file=f)

            if len(restore_st) or len(nonconst_st):
                print("", file=f)
                for s in sorted(restore_st):
                    t = state_types[current_pattern][s]
                    print("    {} = _pmg_backup_{};".format(s, s), file=f)
                for s in sorted(nonconst_st):
                    if s not in restore_st:
                        t = state_types[current_pattern][s]
                        if t.endswith("*"):
                            print("    {} = nullptr;".format(s), file=f)
                        else:
                            print("    {} = {}();".format(s, t), file=f)

        elif block["type"] == "match":
            assert len(restore_st) == 0

            print("    Cell* _pmg_backup_{} = {};".format(block["cell"], block["cell"]), file=f)

            if len(block["if"]):
                for expr in block["if"]:
                    print("", file=f)
                    print("    if (!({})) {{".format(expr), file=f)
                    print("      {} = nullptr;".format(block["cell"]), file=f)
                    print("      block_{}(recursion+1);".format(index+1), file=f)
                    print("      {} = _pmg_backup_{};".format(block["cell"], block["cell"]), file=f)
                    print("      return;", file=f)
                    print("    }", file=f)

            print("", file=f)
            print("    index_{}_key_type key;".format(index), file=f)
            for field, entry in enumerate(block["index"]):
                print("    std::get<{}>(key) = {};".format(field, entry[2]), file=f)
            print("    auto cells_ptr = index_{}.find(key);".format(index), file=f)

            if block["semioptional"] or block["genargs"] is not None:
                print("    bool found_any_match = false;", file=f)

            print("", file=f)
            print("    if (cells_ptr != index_{}.end()) {{".format(index), file=f)
            print("      const vector<index_{}_value_type> &cells = cells_ptr->second;".format(index), file=f)
            print("      for (int _pmg_idx = 0; _pmg_idx < GetSize(cells); _pmg_idx++) {", file=f)
            print("        {} = std::get<0>(cells[_pmg_idx]);".format(block["cell"]), file=f)
            valueidx = 1
            for item in block["setup"]:
                if item[0] == "slice":
                    print("        const int &{} YS_ATTRIBUTE(unused) = std::get<{}>(cells[_pmg_idx]);".format(item[1], valueidx), file=f)
                    valueidx += 1
                if item[0] == "choice":
                    print("        const {} &{} YS_ATTRIBUTE(unused) = std::get<{}>(cells[_pmg_idx]);".format(item[1], item[2], valueidx), file=f)
                    valueidx += 1
                if item[0] == "define":
                    print("        const {} &{} YS_ATTRIBUTE(unused) = std::get<{}>(cells[_pmg_idx]);".format(item[1], item[2], valueidx), file=f)
                    valueidx += 1
            print("        if (blacklist_cells.count({})) continue;".format(block["cell"]), file=f)
            for expr in block["filter"]:
                print("        if (!({})) continue;".format(expr), file=f)
            if block["semioptional"] or block["genargs"] is not None:
                print("        found_any_match = true;", file=f)
            for item in block["sets"]:
                print("        auto _pmg_backup_{} = {};".format(item[0], item[0]), file=f)
                print("        {} = {};".format(item[0], item[1]), file=f)
            print("        auto rollback_ptr = rollback_cache.insert(make_pair(std::get<0>(cells[_pmg_idx]), recursion));", file=f)
            print("        block_{}(recursion+1);".format(index+1), file=f)
            for item in block["sets"]:
                print("        {} = _pmg_backup_{};".format(item[0], item[0]), file=f)
            print("        if (rollback_ptr.second)", file=f)
            print("          rollback_cache.erase(rollback_ptr.first);", file=f)
            print("        if (rollback) {", file=f)
            print("          if (rollback != recursion) {{".format(index+1), file=f)
            print("            {} = _pmg_backup_{};".format(block["cell"], block["cell"]), file=f)
            print("            return;", file=f)
            print("          }", file=f)
            print("          rollback = 0;", file=f)
            print("        }", file=f)
            print("      }", file=f)
            print("    }", file=f)

            print("", file=f)
            print("    {} = nullptr;".format(block["cell"]), file=f)

            if block["optional"]:
                print("    block_{}(recursion+1);".format(index+1), file=f)

            if block["semioptional"]:
                print("    if (!found_any_match) block_{}(recursion+1);".format(index+1), file=f)

            print("    {} = _pmg_backup_{};".format(block["cell"], block["cell"]), file=f)

            if block["genargs"] is not None:
                print("#define finish do { rollback = -1; return; } while(0)", file=f)
                print("    if (generate_mode && rng(100) < (found_any_match ? {} : {})) {{".format(block["genargs"][1], block["genargs"][0]), file=f)
                for line in block["gencode"]:
                    print("      " + line, file=f)
                print("    }", file=f)
                print("#undef finish", file=f)
        else:
            assert False

        current_pattern = None
        print("  }", file=f)
        print("", file=f)

    print("};", file=f)

    if genhdr:
        print("", file=f)
        print("YOSYS_NAMESPACE_END", file=f)
