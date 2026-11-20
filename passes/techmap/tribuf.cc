/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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
#include "kernel/utils.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct TribufConfig {
	bool merge_mode;
	bool logic_mode;
	bool formal_mode;

	TribufConfig() {
		merge_mode = false;
		logic_mode = false;
		formal_mode = false;
	}
};

class TribufCells {
	dict<SigSpec, vector<Cell*>> cells = {};
	void mux_to_tribufs(Cell* cell, Module* module, SigMap& sigmap)
	{
		bool is_fine = cell->type == ID($_MUX_);
		SigSpec sig_a = cell->getPort(ID::A);
		SigSpec sig_b = cell->getPort(ID::B);
		SigSpec sig_s = cell->getPort(ID::S);
		SigSpec sig_y = cell->getPort(ID::Y);
		std::string src = cell->get_src_attribute();

		// Slice the tribuf based on the z-ness of A and B
		SigSpec mux_a, mux_b, mux_y, s_a, s_y, ns_a, ns_y, off_y;
		for (int i = 0; i < GetSize(sig_y); i++) {
			bool z_a = sig_a[i] == State::Sz;
			bool z_b = sig_b[i] == State::Sz;
			if (z_a && z_b) {
				// y = s ? 'z : 'z -> y = $tribuf(A='x, EN='0)
				off_y.append(sig_y[i]);
			} else if (z_a) {
				// y = s ? b : 'z -> y = $tribuf(A=b, EN=s)
				s_a.append(sig_b[i]);
				s_y.append(sig_y[i]);
			} else if (z_b) {
				// y = s ? 'z : a -> y = $tribuf(A=a, EN=~s)
				ns_a.append(sig_a[i]);
				ns_y.append(sig_y[i]);
			} else {
				// No change
				mux_a.append(sig_a[i]);
				mux_b.append(sig_b[i]);
				mux_y.append(sig_y[i]);
			}
		}

		vector<std::tuple<SigSpec, SigSpec, SigSpec>> drivers = {};
		if (!s_y.empty())
			drivers.emplace_back(s_a, sig_s, s_y);
		if (!ns_y.empty())
			drivers.emplace_back(ns_a, is_fine ? SigSpec(module->NotGate(NEW_ID, sig_s, src)) : module->Not(NEW_ID, sig_s, false, src), ns_y);
		if (!off_y.empty())
			drivers.emplace_back(SigSpec(State::Sx, GetSize(off_y)), State::S0, off_y);

		if (!mux_y.empty()) {
			cell->setPort(ID::A, mux_a);
			cell->setPort(ID::B, mux_b);
			cell->setPort(ID::Y, mux_y);
			cell->setParam(ID::WIDTH, GetSize(mux_y));
		}

		for (int i = 0; i < GetSize(drivers); i++) {
			auto &[a, en, y] = drivers[i];
			Cell *tribuf;
			if (i == 0 && mux_y.empty()) {
				tribuf = cell;
				tribuf->unsetPort(ID::B);
				tribuf->unsetPort(ID::S);
				tribuf->type = is_fine ? ID($_TBUF_) : ID($tribuf);
				tribuf->setPort(ID::A, a);
				tribuf->setPort(is_fine ? ID::E : ID::EN, en);
				tribuf->setPort(ID::Y, y);
				if (!is_fine)
					tribuf->setParam(ID::WIDTH, GetSize(y));
			} else {
				tribuf = module->addTribuf(NEW_ID, a, en, y);
				tribuf->attributes = cell->attributes;
			}
			cells[sigmap(y)].push_back(tribuf);
		}

		module->design->scratchpad_set_bool("tribuf.added_something", true);
	}

	class DriverSlices {
		dict<SigSpec, vector<SigSpec>> slices_of_driver = {};
    public:
		DriverSlices(const TribufCells &tribuf_cells)
		{
			vector<SigSpec> driver_sigs = {};
			dict<SigBit, vector<int>> drivers_of_bit = {};
			for (auto &[driver_sig, _] : tribuf_cells.cells) {
				for (auto bit : driver_sig)
					drivers_of_bit[bit].push_back(GetSize(driver_sigs));
				driver_sigs.push_back(driver_sig);
			}

			dict<vector<int>, SigSpec> bits_of_drivers = {};
			for (auto &[bit, drivers] : reversed(drivers_of_bit))
				bits_of_drivers[drivers].append(bit);

			for (auto &[drivers, bits] : bits_of_drivers)
				for (int driver : drivers)
					slices_of_driver[driver_sigs[driver]].push_back(bits);
		}

		// Groups of this driver's bits that share the exact same driver set
		const vector<SigSpec> &slices_of(const SigSpec &driver_sig) const
		{
			return slices_of_driver.at(driver_sig);
		}

		bool is_aligned(const SigSpec &driver_sig) const
		{
			return slices_of(driver_sig)[0] == driver_sig;
		}
	};

	static Cell *slice_tribuf(Module *module, Cell *cell, const dict<SigBit, int> &y_index, const SigSpec &slice)
	{
		SigSpec a = cell->getPort(ID::A);
		SigSpec slice_a = {};
		for (auto bit : slice)
			slice_a.append(a[y_index.at(bit)]);

		Cell *sliced = module->addTribuf(NEW_ID, slice_a, cell->getPort(ID::EN), slice);
		sliced->attributes = cell->attributes;
		return sliced;
	}

public:
	TribufCells(Module* module, SigMap& sigmap) {
		for (auto cell : module->selected_cells())
		{
			if (cell->type == ID($tribuf))
				cells[sigmap(cell->getPort(ID::Y))].push_back(cell);

			if (cell->type == ID($_TBUF_))
				cells[sigmap(cell->getPort(ID::Y))].push_back(cell);

			if (cell->type.in(ID($mux), ID($_MUX_)) && (cell->getPort(ID::A).has_const(State::Sz) || cell->getPort(ID::B).has_const(State::Sz)))
				mux_to_tribufs(cell, module, sigmap);
		}
	}

	auto begin() const { return cells.begin(); }
	auto end() const { return cells.end(); }

	// Slice each net's tribuf outputs into groups of bits driven by the same set of tribuf outputs.
	// Two fully connected tribuf outputs are handled as the same output thanks to prior SigMap,
	// so we're only splitting on partial overlaps
	void split_partial_overlaps(Module *module)
	{
		DriverSlices slices(*this);

		vector<SigSpec> to_split = {};
		for (auto &[y, tribufs] : cells)
			if (!y.empty() && !slices.is_aligned(y))
				to_split.push_back(y);

		for (auto &y : to_split) {
			vector<Cell*> tribufs = std::move(cells.at(y));
			cells.erase(y);

			dict<SigBit, int> y_index = {};
			for (int i = 0; i < GetSize(y); i++)
				y_index[y[i]] = i;

			for (auto &slice : slices.slices_of(y))
				for (auto cell : tribufs)
					cells[slice].push_back(slice_tribuf(module, cell, y_index, slice));

			for (auto cell : tribufs)
				module->remove(cell);
		}
	}
};

static pool<SigBit> get_output_port_bits(Module* module, SigMap& sigmap) {
	pool<SigBit> bits = {};
	for (auto wire : module->wires())
		if (wire->port_output)
			for (auto bit : sigmap(wire))
				bits.insert(bit);
	return bits;
}

class LogicConversion {
	const TribufConfig &config;
	pool<SigBit> output_bits = {};
public:
	LogicConversion(Module *module, SigMap &sigmap, const TribufConfig &config) : config(config)
	{
		if (config.logic_mode && !config.formal_mode)
			output_bits = get_output_port_bits(module, sigmap);
	}

	bool to_logic(const SigSpec &y) const
	{
		if (config.formal_mode)
			return true;
		if (!config.logic_mode)
			return false;
		for (auto bit : y)
			if (output_bits.count(bit))
				return false;
		return true;
	}
};

static SigSpec enable_of(Cell *cell)
{
	return cell->getPort(cell->type == ID($tribuf) ? ID::EN : ID::E);
}

static SigSpec enables_of(const vector<Cell*> &tribufs)
{
	SigSpec enables = {};
	for (auto cell : tribufs)
		enables.append(enable_of(cell));
	return enables;
}

struct TribufWorker {
	Module *module;
	SigMap sigmap;
	const TribufConfig &config;

	TribufWorker(Module *module, const TribufConfig &config) : module(module), sigmap(module), config(config)
	{
	}

	void add_conflict_asserts(const vector<Cell*> &tribufs)
	{
		// Done if nothing can conflict
		if (GetSize(tribufs) <= 1)
			return;

		for (auto cell : tribufs) {
			SigSpec others_s = {};
			for (auto other_cell : tribufs)
				if (other_cell != cell)
					others_s.append(enable_of(other_cell));

			auto other_s = module->ReduceOr(NEW_ID, others_s);
			auto conflict = module->And(NEW_ID, enable_of(cell), other_s);

			std::string name = stringf("$tribuf_conflict$%s", cell);
			auto assert_cell = module->addAssert(name, module->Not(NEW_ID, conflict), SigSpec(true));

			assert_cell->set_src_attribute(cell->get_src_attribute());
			assert_cell->set_bool_attribute(ID::keep);

			module->design->scratchpad_set_bool("tribuf.added_something", true);
		}
	}

	SigSpec merged_data(const SigSpec &y, const vector<Cell*> &tribufs, const SigSpec &enables)
	{
		SigSpec data = {};
		for (auto cell : tribufs)
			data.append(cell->getPort(ID::A));

		if (GetSize(tribufs) == 1)
			return data;
		return module->Pmux(NEW_ID, SigSpec(State::Sx, GetSize(y)), data, enables);
	}

	void merge_net(const SigSpec &y, const vector<Cell*> &tribufs, bool convert_to_logic)
	{
		// Done if nothing to merge or convert
		if (GetSize(tribufs) <= 1 && !convert_to_logic)
			return;

		SigSpec enables = enables_of(tribufs);
		SigSpec data = merged_data(y, tribufs, enables);

		if (convert_to_logic)
			module->connect(y, data);
		else {
			module->addTribuf(NEW_ID, data, module->ReduceOr(NEW_ID, enables), y);
			module->design->scratchpad_set_bool("tribuf.added_something", true);
		}

		for (auto cell : tribufs)
			module->remove(cell);
	}

	void run()
	{
		// Convert elligible $mux to $tribuf and collect all $tribuf
		TribufCells tribuf_cells(module, sigmap);

		if (!config.merge_mode && !config.logic_mode && !config.formal_mode)
			return;

		LogicConversion conversion(module, sigmap, config);
		tribuf_cells.split_partial_overlaps(module);
		for (auto &[y, tribufs] : tribuf_cells) {
			if (config.formal_mode)
				add_conflict_asserts(tribufs);
			merge_net(y, tribufs, conversion.to_logic(y));
		}
	}
};

struct TribufPass : public Pass {
	TribufPass() : Pass("tribuf", "infer tri-state buffers") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    tribuf [options] [selection]\n");
		log("\n");
		log("This pass transforms $mux cells with 'z' inputs to tristate buffers.\n");
		log("\n");
		log("    -merge\n");
		log("        merge multiple tri-state buffers driving the same net\n");
		log("        into a single buffer.\n");
		log("\n");
		log("    -logic\n");
		log("        convert tri-state buffers that do not drive output ports\n");
		log("        to non-tristate logic. this option implies -merge.\n");
		log("\n");
		log("    -formal\n");
		log("        convert all tri-state buffers to non-tristate logic and\n");
		log("        add a formal assertion that no two buffers are driving the\n");
		log("        same net simultaneously. this option implies -merge.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		TribufConfig config;

		log_header(design, "Executing TRIBUF pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-merge") {
				config.merge_mode = true;
				continue;
			}
			if (args[argidx] == "-logic") {
				config.logic_mode = true;
				continue;
			}
			if (args[argidx] == "-formal") {
				config.formal_mode = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules()) {
			TribufWorker worker(module, config);
			worker.run();
		}
	}
} TribufPass;

PRIVATE_NAMESPACE_END
