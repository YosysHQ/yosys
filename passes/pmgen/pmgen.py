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
patterns = dict()
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

def process_pmgfile(f):
    global current_pattern
    while True:
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
                block["pattern"] = current_pattern
                blocks.append(block)
            line = line.split()
            assert len(line) == 2
            assert line[1] not in patterns
            current_pattern = line[1]
            patterns[current_pattern] = len(blocks)
            state_types[current_pattern] = dict()
            udata_types[current_pattern] = dict()
            continue

        assert current_pattern is not None

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
            block["pattern"] = current_pattern

            line = line.split()
            assert len(line) == 2
            assert line[1] not in state_types[current_pattern]
            block["cell"] = line[1]
            state_types[current_pattern][line[1]] = "Cell*";

            block["if"] = list()
            block["select"] = list()
            block["index"] = list()
            block["filter"] = list()
            block["optional"] = False

            while True:
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
                    block["select"].append(rewrite_cpp(b.strip()))
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

                if a[0] == "optional":
                    block["optional"] = True
                    continue

                assert False

            blocks.append(block)
            continue

        if cmd == "code":
            block = dict()
            block["type"] = "code"
            block["pattern"] = current_pattern

            block["code"] = list()
            block["states"] = set()

            for s in line.split()[1:]:
                assert s in state_types[current_pattern]
                block["states"].add(s)

            while True:
                l = f.readline()
                assert l != ""
                a = l.split()
                if len(a) == 0: continue
                if a[0] == "endcode": break

                block["code"].append(rewrite_cpp(l.rstrip()))

            blocks.append(block)
            continue

        assert False

for fn in pmgfiles:
    with open(fn, "r") as f:
        process_pmgfile(f)

if current_pattern is not None:
    block = dict()
    block["type"] = "final"
    block["pattern"] = current_pattern
    blocks.append(block)

current_pattern = None

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
    print("  std::function<void()> on_accept;".format(prefix), file=f)
    print("", file=f)

    for index in range(len(blocks)):
        block = blocks[index]
        if block["type"] == "match":
            index_types = list()
            for entry in block["index"]:
                index_types.append(entry[0])
            print("  typedef std::tuple<{}> index_{}_key_type;".format(", ".join(index_types), index), file=f)
            print("  dict<index_{}_key_type, vector<Cell*>> index_{};".format(index, index), file=f)
    print("  dict<SigBit, pool<Cell*>> sigusers;", file=f)
    print("  pool<Cell*> blacklist_cells;", file=f)
    print("  pool<Cell*> autoremove_cells;", file=f)
    print("  bool blacklist_dirty;", file=f)
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
    print("      if (sigusers.count(bit) == 0 && bit.wire->port_id)", file=f)
    print("        sigusers[bit].insert(nullptr);", file=f)
    print("      sigusers[bit].insert(cell);", file=f)
    print("    }", file=f)
    print("  }", file=f)
    print("", file=f)

    print("  void blacklist(Cell *cell) {", file=f)
    print("    if (cell != nullptr) {", file=f)
    print("      if (blacklist_cells.insert(cell).second)", file=f)
    print("        blacklist_dirty = true;", file=f)
    print("    }", file=f)
    print("  }", file=f)
    print("", file=f)

    print("  void autoremove(Cell *cell) {", file=f)
    print("    if (cell != nullptr) {", file=f)
    print("      if (blacklist_cells.insert(cell).second)", file=f)
    print("        blacklist_dirty = true;", file=f)
    print("      autoremove_cells.insert(cell);", file=f)
    print("    }", file=f)
    print("  }", file=f)
    print("", file=f)

    for current_pattern in sorted(patterns.keys()):
        print("  void check_blacklist_{}() {{".format(current_pattern), file=f)
        print("    if (!blacklist_dirty)", file=f)
        print("      return;", file=f)
        print("    blacklist_dirty = false;", file=f)
        for index in range(len(blocks)):
            block = blocks[index]
            if block["pattern"] != current_pattern:
                continue
            if block["type"] == "match":
                print("    if (st_{}.{} != nullptr && blacklist_cells.count(st_{}.{})) {{".format(current_pattern, block["cell"], current_pattern, block["cell"]), file=f)
                print("      rollback = {};".format(index+1), file=f)
                print("      return;", file=f)
                print("    }", file=f)
        print("    rollback = 0;", file=f)
        print("  }", file=f)
        print("", file=f)
    current_pattern = None

    print("  SigSpec port(Cell *cell, IdString portname) {", file=f)
    print("    return sigmap(cell->getPort(portname));", file=f)
    print("  }", file=f)
    print("", file=f)

    print("  Const param(Cell *cell, IdString paramname) {", file=f)
    print("    return cell->getParam(paramname);", file=f)
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
    print("      module(module), sigmap(module) {", file=f)
    for current_pattern in sorted(patterns.keys()):
        for s, t in sorted(udata_types[current_pattern].items()):
            if t.endswith("*"):
                print("    ud_{}.{} = nullptr;".format(current_pattern,s), file=f)
            else:
                print("    ud_{}.{} = {}();".format(current_pattern, s, t), file=f)
    current_pattern = None
    print("    for (auto cell : module->cells()) {", file=f)
    print("      for (auto &conn : cell->connections())", file=f)
    print("        add_siguser(conn.second, cell);", file=f)
    print("    }", file=f)
    print("    for (auto cell : cells) {", file=f)

    for index in range(len(blocks)):
        block = blocks[index]
        if block["type"] == "match":
            print("      do {", file=f)
            print("        Cell *{} = cell;".format(block["cell"]), file=f)
            for expr in block["select"]:
                print("        if (!({})) break;".format(expr), file=f)
            print("        index_{}_key_type key;".format(index), file=f)
            for field, entry in enumerate(block["index"]):
                print("        std::get<{}>(key) = {};".format(field, entry[1]), file=f)
            print("        index_{}[key].push_back(cell);".format(index), file=f)
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
        print("  void run_{}(std::function<void()> on_accept_f) {{".format(current_pattern), file=f)
        print("    on_accept = on_accept_f;", file=f)
        print("    rollback = 0;", file=f)
        print("    blacklist_dirty = false;", file=f)
        for s, t in sorted(state_types[current_pattern].items()):
            if t.endswith("*"):
                print("    st_{}.{} = nullptr;".format(current_pattern, s), file=f)
            else:
                print("    st_{}.{} = {}();".format(current_pattern, s, t), file=f)
        print("    block_{}();".format(patterns[current_pattern]), file=f)
        print("  }", file=f)
        print("", file=f)
        print("  void run_{}(std::function<void({}_pm&)> on_accept_f) {{".format(current_pattern, prefix), file=f)
        print("    run_{}([&](){{on_accept_f(*this);}});".format(current_pattern), file=f)
        print("  }", file=f)
        print("", file=f)
        print("  void run_{}(std::function<void(state_{}_t&)> on_accept_f) {{".format(current_pattern, current_pattern), file=f)
        print("    run_{}([&](){{on_accept_f(st_{});}});".format(current_pattern, current_pattern), file=f)
        print("  }", file=f)
        print("", file=f)
        print("  void run_{}() {{".format(current_pattern), file=f)
        print("    run_{}([](){{}});".format(current_pattern, current_pattern), file=f)
        print("  }", file=f)
        print("", file=f)
    current_pattern = None

    for index in range(len(blocks)):
        block = blocks[index]

        print("  void block_{}() {{".format(index), file=f)
        current_pattern = block["pattern"]

        if block["type"] == "final":
            print("    on_accept();", file=f)
            print("    check_blacklist_{}();".format(current_pattern), file=f)
            print("  }", file=f)
            if index+1 != len(blocks):
                print("", file=f)
            continue

        const_st = set()
        nonconst_st = set()
        restore_st = set()

        for i in range(patterns[current_pattern], index):
            if blocks[i]["type"] == "code":
                for s in blocks[i]["states"]:
                    const_st.add(s)
            elif blocks[i]["type"] == "match":
                const_st.add(blocks[i]["cell"])
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

        if len(restore_st):
            print("", file=f)
            for s in sorted(restore_st):
                t = state_types[current_pattern][s]
                print("    {} backup_{} = {};".format(t, s, s), file=f)

        if block["type"] == "code":
            print("", file=f)
            print("    do {", file=f)
            print("#define reject do {{ check_blacklist_{}(); goto rollback_label; }} while(0)".format(current_pattern), file=f)
            print("#define accept do {{ on_accept(); check_blacklist_{}(); if (rollback) goto rollback_label; }} while(0)".format(current_pattern), file=f)
            print("#define branch do {{ block_{}(); if (rollback) goto rollback_label; }} while(0)".format(index+1), file=f)

            for line in block["code"]:
                print("    " + line, file=f)

            print("", file=f)
            print("      block_{}();".format(index+1), file=f)
            print("#undef reject", file=f)
            print("#undef accept", file=f)
            print("#undef branch", file=f)
            print("    } while (0);", file=f)
            print("", file=f)
            print("rollback_label:", file=f)
            print("    YS_ATTRIBUTE(unused);", file=f)

            if len(restore_st) or len(nonconst_st):
                print("", file=f)
                for s in sorted(restore_st):
                    t = state_types[current_pattern][s]
                    print("    {} = backup_{};".format(s, s), file=f)
                for s in sorted(nonconst_st):
                    if s not in restore_st:
                        t = state_types[current_pattern][s]
                        if t.endswith("*"):
                            print("    {} = nullptr;".format(s), file=f)
                        else:
                            print("    {} = {}();".format(s, t), file=f)

        elif block["type"] == "match":
            assert len(restore_st) == 0

            if len(block["if"]):
                for expr in block["if"]:
                    print("", file=f)
                    print("    if (!({})) {{".format(expr), file=f)
                    print("      {} = nullptr;".format(block["cell"]), file=f)
                    print("      block_{}();".format(index+1), file=f)
                    print("      return;", file=f)
                    print("    }", file=f)

            print("", file=f)
            print("    index_{}_key_type key;".format(index), file=f)
            for field, entry in enumerate(block["index"]):
                print("    std::get<{}>(key) = {};".format(field, entry[2]), file=f)
            print("    const vector<Cell*> &cells = index_{}[key];".format(index), file=f)

            print("", file=f)
            print("    for (int idx = 0; idx < GetSize(cells); idx++) {", file=f)
            print("      {} = cells[idx];".format(block["cell"]), file=f)
            print("      if (blacklist_cells.count({})) continue;".format(block["cell"]), file=f)
            for expr in block["filter"]:
                print("      if (!({})) continue;".format(expr), file=f)
            print("      block_{}();".format(index+1), file=f)
            print("      if (rollback) {", file=f)
            print("        if (rollback != {}) {{".format(index+1), file=f)
            print("          {} = nullptr;".format(block["cell"]), file=f)
            print("          return;", file=f)
            print("        }", file=f)
            print("        rollback = 0;", file=f)
            print("      }", file=f)
            print("    }", file=f)

            print("", file=f)
            print("    {} = nullptr;".format(block["cell"]), file=f)

            if block["optional"]:
                print("    block_{}();".format(index+1), file=f)

        else:
            assert False

        current_pattern = None
        print("  }", file=f)
        print("", file=f)

    print("};", file=f)

    if genhdr:
        print("", file=f)
        print("YOSYS_NAMESPACE_END", file=f)
