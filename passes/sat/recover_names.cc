/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2021 gatecat <gatecat@ds0.me>
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
#include "kernel/consteval.h"
#include "kernel/celltypes.h"
#include "kernel/utils.h"
#include "kernel/satgen.h"

#include <algorithm>
#include <queue>
#include <cinttypes>

USING_YOSYS_NAMESPACE

PRIVATE_NAMESPACE_BEGIN

// xorshift128 params
#define INIT_X 123456789
#define INIT_Y 362436069
#define INIT_Z 521288629
#define INIT_W  88675123


// Similar to a SigBit; but module-independent
struct IdBit {
    IdBit() : name(), bit(0) {};
    IdBit(IdString name, int bit = 0) : name(name), bit(bit) {};

    bool operator==(const IdBit &other) const { return name == other.name && bit == other.bit; };
    bool operator!=(const IdBit &other) const { return name != other.name || bit != other.bit; };
    unsigned hash() const
    {
        return mkhash_add(name.hash(), bit);
    }

    IdString name;
    int bit;
};

// As above; but can be inverted
struct InvBit {
    InvBit() : bit(), inverted(false) {};
    explicit InvBit(IdBit bit, bool inverted = false) : bit(bit), inverted(inverted) {};

    bool operator==(const InvBit &other) const { return bit == other.bit && inverted == other.inverted; };
    bool operator!=(const InvBit &other) const { return bit != other.bit || inverted != other.inverted; };
    unsigned hash() const
    {
        return mkhash(bit.hash(), inverted);
    }

    IdBit bit;
    bool inverted;
};

typedef uint64_t equiv_cls_t;
static const int sim_length = sizeof(equiv_cls_t) * 8;

struct RecoverModuleWorker {
    Design *design = nullptr;
    Module *mod, *flat = nullptr;
    RecoverModuleWorker(Module *mod) : design(mod->design), mod(mod) {};

    ConstEval *ce = nullptr;
    SigMap *sigmap = nullptr;

    dict<IdBit, SigBit> flat2orig;
    dict<IdBit, IdBit> bit2primary;
    dict<IdBit, Cell*> bit2driver;

    void prepare()
    {
        // Create a derivative of the module with whiteboxes flattened so we can
        // run eval and sat on it
        flat = design->addModule(NEW_ID);
        mod->cloneInto(flat);
        Pass::call_on_module(design, flat, "flatten -wb");
        ce = new ConstEval(flat);
        sigmap = new SigMap(flat);
        // Create a mapping from primary name-bit in the box-flattened module to original sigbit
        SigMap orig_sigmap(mod);
        for (auto wire : mod->wires()) {
            Wire *flat_wire = flat->wire(wire->name);
            if (!flat_wire)
                continue;
            for (int i = 0; i < wire->width; i++) {
                SigBit orig_sigbit = orig_sigmap(SigBit(wire, i));
                SigBit flat_sigbit = (*sigmap)(SigBit(flat_wire, i));
                if (!orig_sigbit.wire || !flat_sigbit.wire)
                    continue;
                flat2orig[IdBit(flat_sigbit.wire->name, flat_sigbit.offset)] = orig_sigbit;
            }
        }
        find_driven_bits();
    }

    void find_driven_bits()
    {
        // Add primary inputs
        for (auto wire : flat->wires()) {
            if (!wire->port_input)
                continue;
            for (int i = 0; i < wire->width; i++) {
                SigBit bit(wire, i);
                bit = (*sigmap)(bit);
                if (bit.wire)
                    bit2driver[IdBit(bit.wire->name, bit.offset)] = nullptr;
            }
        }
        // Add cell outputs
        for (auto cell : flat->cells()) {
            for (auto conn : cell->connections()) {
                if (!cell->output(conn.first))
                    continue;
                for (auto bit : conn.second) {
                    auto resolved = (*sigmap)(bit);
                    if (resolved.wire)
                        bit2driver[IdBit(resolved.wire->name, resolved.offset)] = cell;
                }
            }
        }
        // Setup bit2primary
        for (auto wire : flat->wires()) {
            for (int i = 0; i < wire->width; i++) {
                SigBit bit(wire, i);
                bit = (*sigmap)(bit);
                if (bit.wire)
                    bit2primary[IdBit(wire->name, i)] = IdBit(bit.wire->name, bit.offset);
            }
        }
    }

    // Mapping from bit to (candidate) equivalence classes
    dict<IdBit, equiv_cls_t> bit2cls;
    void sim_cycle(int t, const dict<IdBit, RTLIL::State> &anchors)
    {
        ce->clear();
        for (auto anchor : anchors) {
            SigBit bit = (*sigmap)(SigBit(flat->wire(anchor.first.name), anchor.first.bit));
            // Ignore in the rare case that it's already determined
            SigSpec res(bit);
            if (ce->eval(res))
                continue;
            ce->set(bit, anchor.second);
        }
        // Only evaluate IdBits that exist in the non-flat design; as they are all we care about
        for (auto idbit : flat2orig) {
            if (anchors.count(idbit.first))
                continue;
            SigBit bit = (*sigmap)(SigBit(flat->wire(idbit.first.name), idbit.first.bit));
            SigSpec res(bit);
            if (!ce->eval(res))
                continue;
            if (res != State::S0 && res != State::S1)
                continue;
            // Update equivalence classes
            if (res == State::S1)
                bit2cls[idbit.first] = bit2cls[idbit.first] | (equiv_cls_t(1) << t);
        }
    }

    // Update the equivalence class groupings
    void group_classes(dict<equiv_cls_t, std::pair<pool<IdBit>, pool<InvBit>>> &cls2bits, bool is_gate)
    {
        equiv_cls_t all_ones = 0;
        for (int i = 0; i < sim_length; i++) all_ones |= (equiv_cls_t(1) << i);
        for (auto pair : bit2cls) {
            if (pair.second == 0 || pair.second == all_ones)
                continue; // skip stuck-ats
            if (is_gate) {
                // True doesn't exist in gold; but inverted does
                if (!cls2bits.count(pair.second) && cls2bits.count(pair.second ^ all_ones))
                    cls2bits[pair.second ^ all_ones].second.emplace(pair.first, true);
                else
                    cls2bits[pair.second].second.emplace(pair.first, false);
            } else {
                cls2bits[pair.second].first.insert(pair.first);
            }
        }
    }

    // Compute depths of IdBits
    dict<IdBit, int> bit2depth;
    void compute_depths(const dict<IdBit, IdBit> &anchor_bits)
    {
        dict<SigBit, pool<IdString>> bit_drivers, bit_users;
        TopoSort<IdString, RTLIL::sort_by_id_str> toposort;

        for (auto cell : flat->cells())
        for (auto conn : cell->connections())
        {
            for (auto bit : (*sigmap)(conn.second)) {
                if (!bit.wire)
                    continue;
                IdBit idbit(bit.wire->name, bit.offset);
                if (anchor_bits.count(idbit))
                    continue;
                if (cell->input(conn.first))
                    bit_users[bit].insert(cell->name);

                if (cell->output(conn.first))
                    bit_drivers[bit].insert(cell->name);
            }

            toposort.node(cell->name);
        }

        for (auto &it : bit_users)
            if (bit_drivers.count(it.first))
                for (auto driver_cell : bit_drivers.at(it.first))
                for (auto user_cell : it.second)
                    toposort.edge(driver_cell, user_cell);

        toposort.sort();
        for (auto cell_name : toposort.sorted) {
            Cell *cell = flat->cell(cell_name);
            int cell_depth = 0;
            for (auto conn : cell->connections()) {
                if (!cell->input(conn.first))
                    continue;
                for (auto bit : (*sigmap)(conn.second)) {
                    if (!bit.wire)
                        continue;
                    IdBit idbit(bit.wire->name, bit.offset);
                    if (!bit2depth.count(idbit))
                        continue;
                    cell_depth = std::max(cell_depth, bit2depth.at(idbit));
                }
            }
            for (auto conn : cell->connections()) {
                if (!cell->output(conn.first))
                    continue;
                for (auto bit : (*sigmap)(conn.second)) {
                    if (!bit.wire)
                        continue;
                    IdBit idbit(bit.wire->name, bit.offset);
                    bit2depth[idbit] = std::max(bit2depth[idbit], cell_depth + 1);
                }
            }
        }
    }

    // SAT thresholds
    const int max_sat_cells = 50;

    SigBit id2bit(IdBit bit) { return SigBit(flat->wire(bit.name), bit.bit); }

    // Set up the SAT problem for an IdBit
    // the value side of 'anchors' will be populated with the SAT variable for anchor bits
    int setup_sat(SatGen *sat, const std::string &prefix, IdBit bit, const dict<IdBit, IdBit> &anchor_bits, dict<IdBit, int> &anchor2var)
    {
        sat->setContext(sigmap, prefix);
        pool<IdString> imported_cells;
        int result = sat->importSigBit(id2bit(bit));
        // Recursively import driving cells
        std::queue<IdBit> to_import;
        to_import.push(bit);
        while (!to_import.empty()) {
            // Too many cells imported
            if (GetSize(imported_cells) > max_sat_cells)
                return -1;
            IdBit cursor = to_import.front();
            to_import.pop();
            if (anchor_bits.count(cursor)) {
                if (!anchor2var.count(cursor)) {
                    anchor2var[cursor] = sat->importSigBit(id2bit(cursor));
                }
                continue;
            }
            // Import driver if it exists
            if (!bit2driver.count(cursor))
                continue;
            Cell *driver = bit2driver.at(cursor);
            if (!driver || imported_cells.count(driver->name))
                continue;
            if (!sat->importCell(driver))
                return -1; // cell can't be imported
            imported_cells.insert(driver->name);
            // Add cell inputs to queue
            for (auto conn : driver->connections()) {
                if (!driver->input(conn.first))
                    continue;
                for (SigBit in_bit : (*sigmap)(conn.second)) {
                    if (!in_bit.wire)
                        continue;
                    IdBit in_idbit(in_bit.wire->name, in_bit.offset);
                    to_import.push(in_idbit);
                }
            }
        }
        return result;
    }

    void find_buffers(const pool<IdString> &buffer_types, dict<SigBit, pool<SigBit>> &root2buffered)
    {
        SigMap orig_sigmap(mod);
        dict<SigBit, SigBit> buffer2root;
        for (auto cell : mod->cells()) {
            if (!buffer_types.count(cell->type))
                continue;
            SigBit in, out;
            for (auto conn : cell->connections()) {
                if (cell->input(conn.first)) {
                    in = orig_sigmap(conn.second[0]);
                }
                if (cell->output(conn.first)) {
                    out = orig_sigmap(conn.second[0]);
                }
            }
            if (!in.wire || !out.wire)
                continue;
            SigBit root = in;
            if (buffer2root.count(root))
                root = buffer2root[root];
            if (root2buffered.count(out)) {
                for (auto out_sig : root2buffered.at(out))
                    root2buffered[root].insert(out_sig);
                root2buffered.erase(out);
            }
            root2buffered[root].insert(out);
            buffer2root[out] = root;
        }
    }

    void do_rename(Module *gold, const dict<IdBit, InvBit> &gate2gold, const pool<IdString> &buffer_types)
    {
        dict<SigBit, std::vector<std::tuple<Cell*, IdString, int>>> bit2port;
        pool<SigBit> unused_bits;
        SigMap orig_sigmap(mod);
        for (auto wire : mod->wires()) {
            if (wire->port_input || wire->port_output)
                continue;
            for (int i = 0; i < wire->width; i++)
                unused_bits.insert(orig_sigmap(SigBit(wire, i)));
        }
        for (auto cell : mod->cells()) {
            for (auto conn : cell->connections()) {
                for (int i = 0; i < GetSize(conn.second); i++) {
                    SigBit bit = orig_sigmap(conn.second[i]);
                    if (!bit.wire)
                        continue;
                    bit2port[bit].emplace_back(cell, conn.first, i);
                    unused_bits.erase(bit);
                }
            }
        }
        dict<SigBit, pool<SigBit>> root2buffered;
        find_buffers(buffer_types, root2buffered);

        // An extension of gate2gold that deals with buffers too
        // gate sigbit --> (new name, invert, gold wire)
        dict<SigBit, std::pair<InvBit, Wire*>> rename_map;
        for (auto pair : gate2gold) {
            SigBit gate_bit = flat2orig.at(pair.first);
            Wire *gold_wire = gold->wire(pair.second.bit.name);
            rename_map[gate_bit] = std::make_pair(pair.second, gold_wire);
            if (root2buffered.count(gate_bit)) {
                int buf_idx = 0;
                for (auto buf_bit : root2buffered.at(gate_bit)) {
                    std::string buf_name_str = stringf("%s_buf_%d", pair.second.bit.name.c_str(), ++buf_idx);
                    if (buf_name_str[0] == '\\')
                        buf_name_str[0] = '$';
                    rename_map[buf_bit] = std::make_pair(
                        InvBit(IdBit(IdString(buf_name_str), pair.second.bit.bit), pair.second.inverted), gold_wire);
                }
            }
        }

        for (auto rule : rename_map) {
            // Pick a uniq new name
            IdBit new_name = rule.second.first.bit;
            int dup_idx = 0;
            bool must_invert_name = rule.second.first.inverted;
            while (must_invert_name ||
                    (mod->wire(new_name.name) && !unused_bits.count(SigBit(mod->wire(new_name.name), new_name.bit)))) {
                std::string new_name_str = stringf("%s_%s_%d", rule.second.first.bit.name.c_str(),
                    rule.second.first.inverted ? "inv" : "dup", ++dup_idx);
                if (new_name_str[0] == '\\')
                    new_name_str[0] = '$';
                new_name.name = IdString(new_name_str);
                must_invert_name = false;
            }
            // Create the wire if needed
            Wire *new_wire = mod->wire(new_name.name);
            if (!new_wire) {
                Wire *gold_wire = rule.second.second;
                new_wire = mod->addWire(new_name.name, gold_wire->width);
                new_wire->start_offset = gold_wire->start_offset;
                new_wire->upto = gold_wire->upto;
                for (const auto &attr : gold_wire->attributes)
                    new_wire->attributes[attr.first] = attr.second;
                for (int i = 0; i < new_wire->width; i++)
                    unused_bits.insert(SigBit(new_wire, i));
            }
            // Ensure it's wide enough
            if (new_wire->width <= new_name.bit)
                new_wire->width = new_name.bit + 1;
            SigBit old_bit = rule.first;
            SigBit new_bit(new_wire, new_name.bit);
            unused_bits.erase(new_bit);
            // Replace all users
            if (bit2port.count(old_bit))
                for (auto port_ref : bit2port.at(old_bit)) {
                    Cell *cell = std::get<0>(port_ref);
                    IdString port_name = std::get<1>(port_ref);
                    int port_bit = std::get<2>(port_ref);
                    SigSpec port_sig = cell->getPort(port_name);
                    port_sig.replace(port_bit, new_bit);
                    cell->unsetPort(port_name);
                    cell->setPort(port_name, port_sig);
                }
        }
    }

    ~RecoverModuleWorker()
    {
        delete ce;
        delete sigmap;
        if (flat)
            design->remove(flat);
    }
};

struct RecoverNamesWorker {
    Design *design, *gold_design = nullptr;
    CellTypes ct_all;
    RecoverNamesWorker(Design *design) : design(design) {}

    pool<IdString> comb_whiteboxes, buffer_types;

    // class -> (gold, (gate, inverted))
    dict<equiv_cls_t, std::pair<pool<IdBit>, dict<IdBit, bool>>> cls2bits;

    void analyse_boxes()
    {
        for (auto mod : design->modules()) {
            if (!mod->get_bool_attribute(ID::whitebox))
                continue;
            bool is_comb = true;
            for (auto cell : mod->cells()) {
                if (ct_all.cell_evaluable(cell->type)) {
                    is_comb = false;
                    break;
                }
            }
            if (!is_comb)
                continue;
            comb_whiteboxes.insert(mod->name);
            // Buffers have one input and one output; exactly
            SigBit in{}, out{};
            ConstEval eval(mod);
            for (auto wire : mod->wires()) {
                if (wire->port_input) {
                    if (wire->width != 1 || in.wire)
                        goto not_buffer;
                    in = SigBit(wire, 0);
                }
                if (wire->port_output) {
                    if (wire->width != 1 || out.wire)
                        goto not_buffer;
                    out = SigBit(wire, 0);
                }
            }
            if (!in.wire || !out.wire)
                goto not_buffer;
            // Buffer input mirrors output
            for (auto bit : {State::S0, State::S1}) {
                eval.clear();
                eval.set(in, bit);
                SigSpec result(out);
                if (!eval.eval(result))
                    goto not_buffer;
                if (result != bit)
                    goto not_buffer;
            }
            buffer_types.insert(mod->name);
            if (false) {
                not_buffer:
                    continue;
            }
        }
        log_debug("Found %d combinational cells and %d buffer whiteboxes.\n", GetSize(comb_whiteboxes), GetSize(buffer_types));
    }

    uint32_t x, y, z, w, rng_val;
    int rng_bit;
    void rng_init()
    {
        x = INIT_X;
        y = INIT_Y;
        z = INIT_Z;
        w = INIT_W;
        rng_bit = 32;
    }
    uint32_t xorshift128()
    {
        uint32_t t = x ^ (x << 11);
        x = y; y = z; z = w;
        w ^= (w >> 19) ^ t ^ (t >> 8);
        return w;
    }
    RTLIL::State next_randbit()
    {
        if (rng_bit >= 32) {
            rng_bit = 0;
            rng_val = xorshift128();
        }
        return ((rng_val >> (rng_bit++)) & 0x1) ? RTLIL::State::S1 : RTLIL::State::S0;
    }

    int popcount(equiv_cls_t cls) {
    	int result = 0;
    	for (unsigned i = 0; i < 8*sizeof(equiv_cls_t); i++)
    		if ((cls >> i) & 0x1)
    			++result;
    	return result;
    }

    bool prove_equiv(RecoverModuleWorker &gold_worker, RecoverModuleWorker &gate_worker,
            const dict<IdBit, IdBit> &gold_anchors, const dict<IdBit, IdBit> &gate_anchors,
            IdBit gold_bit, IdBit gate_bit, bool invert) {
        ezSatPtr ez;
        SatGen satgen(ez.get(), nullptr);
        dict<IdBit, int> anchor2var_gold, anchor2var_gate;
        int gold_var = gold_worker.setup_sat(&satgen, "gold", gold_bit, gold_anchors, anchor2var_gold);
        if (gold_var == -1)
            return false;
        int gate_var = gate_worker.setup_sat(&satgen, "gate", gate_bit, gate_anchors, anchor2var_gate);
        if (gate_var == -1)
            return false;
        // Assume anchors are equal
        for (auto anchor : anchor2var_gate) {
            IdBit gold_anchor = gate_anchors.at(anchor.first);
            if (!anchor2var_gold.count(gold_anchor))
                continue;
            ez->assume(ez->IFF(anchor.second, anchor2var_gold.at(gold_anchor)));
        }
        // Prove equivalence
        return !ez->solve(ez->NOT(ez->IFF(gold_var, invert ? ez->NOT(gate_var) : gate_var)));
    }

    void analyse_mod(Module *gate_mod)
    {
        Module *gold_mod = gold_design->module(gate_mod->name);
        if (!gold_mod)
            return;

        RecoverModuleWorker gold_worker(gold_mod);
        RecoverModuleWorker gate_worker(gate_mod);

        gold_worker.prepare();
        gate_worker.prepare();

        // Find anchors (same-name wire-bits driven in both gold and gate)
        dict<IdBit, IdBit> gold_anchors, gate_anchors;

        for (auto gold_bit : gold_worker.bit2driver) {
            if (gate_worker.bit2primary.count(gold_bit.first)) {
                IdBit gate_bit = gate_worker.bit2primary.at(gold_bit.first);
                if (!gate_worker.bit2driver.count(gate_bit))
                    continue;
                gold_anchors[gold_bit.first] = gate_bit;
                gate_anchors[gate_bit] = gold_bit.first;
            }
        }
        // Run a random-value combinational simulation to find candidate equivalence classes
        dict<IdBit, RTLIL::State> gold_anchor_vals, gate_anchor_vals;
        rng_init();
        for (int t = 0; t < sim_length; t++) {
            for (auto anchor : gold_anchors) {
                gold_anchor_vals[anchor.first] = next_randbit();
                gate_anchor_vals[anchor.second] = gold_anchor_vals[anchor.first];
            }
            gold_worker.sim_cycle(t, gold_anchor_vals);
            gate_worker.sim_cycle(t, gate_anchor_vals);
        }
        log_debug("%d candidate equiv classes in gold; %d in gate\n", GetSize(gold_worker.bit2cls), GetSize(gate_worker.bit2cls));
        // Group bits by equivalence classes together
        dict<equiv_cls_t, std::pair<pool<IdBit>, pool<InvBit>>> cls2bits;
        gold_worker.group_classes(cls2bits, false);
        gate_worker.group_classes(cls2bits, true);
        gate_worker.compute_depths(gate_anchors);
        // Sort equivalence classes by shallowest first (so we have as many anchors as possible when reaching deeper bits)
        std::vector<std::pair<equiv_cls_t, int>> cls_depth;
        for (auto &cls : cls2bits) {
            if (cls.second.second.empty())
                continue;
            int depth = 0;
            for (auto gate_bit : cls.second.second) {
                if (!gate_worker.bit2depth.count(gate_bit.bit))
                    continue;
                depth = std::max(depth, gate_worker.bit2depth.at(gate_bit.bit));
            }
            cls_depth.emplace_back(cls.first, depth);
        }
        std::stable_sort(cls_depth.begin(), cls_depth.end(),
            [](const std::pair<equiv_cls_t, int> &a, const std::pair<equiv_cls_t, int> &b) {
                return a.second < b.second;
            });
        // The magic result we've worked hard for....
        dict<IdBit, InvBit> gate2gold;
        // Solve starting from shallowest
        for (auto cls : cls_depth) {
        	int pop = popcount(cls.first);
        	// Equivalence classes with only one set bit are invariably a waste of SAT time
        	if (pop == 1 || pop == (8*sizeof(equiv_cls_t) - 1))
        		continue;

        	log_debug("equivalence class: %016" PRIx64 "\n", cls.first);
            const pool<IdBit> &gold_bits = cls2bits.at(cls.first).first;
            const pool<InvBit> &gate_bits = cls2bits.at(cls.first).second;
            if (gold_bits.empty() || gate_bits.empty())
                continue;
            pool<IdBit> solved_gate;
            if (GetSize(gold_bits) > 10)
                continue; // large equivalence classes are not very interesting; skip
            for (IdBit gold_bit : gold_bits) {
                for (auto gate_bit : gate_bits) {
                    if (solved_gate.count(gate_bit.bit))
                        continue;
                    log_debug("   attempting to prove %s[%d] == %s%s[%d]\n", log_id(gold_bit.name), gold_bit.bit,
                        gate_bit.inverted ? "" : "!", log_id(gate_bit.bit.name), gate_bit.bit.bit);
                    if (!prove_equiv(gold_worker, gate_worker, gold_anchors, gate_anchors, gold_bit, gate_bit.bit, gate_bit.inverted))
                        continue;
                    log_debug("       success!\n");
                    // Success!
                    gate2gold[gate_bit.bit] = InvBit(gold_bit, gate_bit.inverted);
                    if (!gate_bit.inverted) {
                        // Only add as anchor if not inverted
                        gold_anchors[gold_bit] = gate_bit.bit;
                        gate_anchors[gate_bit.bit] = gold_bit;
                    }
                    solved_gate.insert(gate_bit.bit);
                }
                // All solved...
                if (GetSize(solved_gate) == GetSize(gate_bits))
                    break;
            }
        }
        log("Recovered %d net name pairs in module `%s' out.\n", GetSize(gate2gold), log_id(gate_mod));
        gate_worker.do_rename(gold_mod, gate2gold, buffer_types);
    }

    void operator()(string command)
    {
        // Make a backup copy of the pre-mapping design for later
        gold_design = new RTLIL::Design;

        for (auto mod : design->modules())
            gold_design->add(mod->clone());

        run_pass(command, design);

        analyse_boxes();

        // keeping our own std::vector here avoids modify-while-iterating issues
        std::vector<Module *> to_analyse;
        for (auto mod : design->modules())
            if (!mod->get_blackbox_attribute())
                to_analyse.push_back(mod);
        for (auto mod : to_analyse)
            analyse_mod(mod);
    }
    ~RecoverNamesWorker() {
        delete gold_design;
    }
};

struct RecoverNamesPass : public Pass {
    RecoverNamesPass() : Pass("recover_names", "Execute a lossy mapping command and recover original netnames") { }
    void help() override
    {
        //   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
        log("\n");
        log("    recover_names [command]\n");
        log("\n");
        log("This pass executes a lossy mapping command and uses a combination of simulation\n");
        log(" to find candidate equivalences and SAT to recover exact original net names.\n");
        log("\n");
    }
    void execute(std::vector<std::string> args, RTLIL::Design *design) override
    {
        log_header(design, "Executing RECOVER_NAMES pass (run mapping and recover original names).\n");
        string command;

        size_t argidx = 1;
        for (; argidx < args.size(); argidx++) {
            if (command.empty()) {
                if (args[argidx].compare(0, 1, "-") == 0)
                    cmd_error(args, argidx, "Unknown option.");
            } else {
                command += " ";
            }
            command += args[argidx];
        }

        if (command.empty())
            log_cmd_error("No mapping pass specified!\n");

        RecoverNamesWorker worker(design);
        worker(command);

    }
} RecoverNamesPass;

PRIVATE_NAMESPACE_END
