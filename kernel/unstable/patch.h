#ifndef PATCH_H
#define PATCH_H

#include "kernel/rtlil.h"
#include "kernel/sigtools.h"

YOSYS_NAMESPACE_BEGIN

// No virtual methods — subclasses cannot be dispatched through a Patch pointer.
struct RTLIL::Patch : public CellAdderMixin<RTLIL::Patch>
{
private:
	void gc(Cell* old_cell, bool track = false, pool<std::string>* src_pool = nullptr);

protected:
	void add(RTLIL::Wire *wire);
	void add(RTLIL::Cell *cell);
	void add(RTLIL::Process *process);

	Cell* commit_cell(std::unique_ptr<Cell> cell);
	Wire* commit_wire(std::unique_ptr<Wire> wire);

	pool<Wire*> leaves = {};

public:
	Module* mod;
	SigMap* map;
	pool<Cell*>* removed_cells = nullptr;
	vector<std::unique_ptr<Wire>> wires_ = {};
	vector<std::unique_ptr<Cell>> cells_ = {};

	void connect(const RTLIL::SigSig &conn);
	void connect(const RTLIL::SigSpec &lhs, const RTLIL::SigSpec &rhs);
	const std::vector<RTLIL::SigSig> &connections() const;

	void patch(Cell* old_cell, IdString old_port, SigSpec new_sig);
	void patch(Cell* old_cell, const std::vector<std::pair<IdString, SigSpec>> &port_replacements);

	// Variants for "merge old_cell into an existing keep_cell" (e.g.
	// opt_merge): the old_cell's src attribute is collected and combined
	// with merge_src_into's existing src, and the result is set on
	// merge_src_into. Any new cells in cells_ also receive the combined src.
	void patch(Cell* old_cell, IdString old_port, SigSpec new_sig, Cell* merge_src_into);
	void patch(Cell* old_cell, const std::vector<std::pair<IdString, SigSpec>> &port_replacements, Cell* merge_src_into);

	// Flush staged cells_ / wires_ into the module without doing any
	// connect_incremental or gc. Each committed cell's src attribute is
	// pulled from `src_source` (typically the cell that's being expanded /
	// unmapped into the staged helpers, so source-location tracking carries
	// through transparently). Pass nullptr for src_source if the staged
	// helpers have no natural ancestor.
	void commit_inheriting_src(Cell* src_source);
	RTLIL::Wire *addWire(RTLIL::IdString name, int width = 1);
	RTLIL::Wire *addWire(RTLIL::IdString name, const RTLIL::Wire *other);

	RTLIL::Cell *addCell(RTLIL::IdString name, RTLIL::IdString type);
	RTLIL::Cell *addCell(RTLIL::IdString name, const RTLIL::Cell *other);

	RTLIL::Cell* addDffsr(RTLIL::IdString name, const RTLIL::SigSpec &sig_clk, const RTLIL::SigSpec &sig_set, const RTLIL::SigSpec &sig_clr,
		RTLIL::SigSpec sig_d, const RTLIL::SigSpec &sig_q, bool clk_polarity, bool set_polarity, bool clr_polarity, const std::string &src);

	Patch(Module* mod, SigMap* map = nullptr) : mod(mod), map(map) {}
};

YOSYS_NAMESPACE_END

#endif
