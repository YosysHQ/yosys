#ifndef PATCH_H
#define PATCH_H

#include "kernel/rtlil.h"
#include "kernel/sigtools.h"

YOSYS_NAMESPACE_BEGIN

// No virtual methods — subclasses cannot be dispatched through a Patch pointer.
struct RTLIL::Patch : public CellAdderMixin<RTLIL::Patch>
{
protected:
	void add(RTLIL::Wire *wire);
	void add(RTLIL::Cell *cell);
	void add(RTLIL::Process *process);

	Cell* commit_cell(std::unique_ptr<Cell> cell);
	Wire* commit_wire(std::unique_ptr<Wire> wire);

	// Move staged cells_/wires_ into the module. Returns raw pointers to
	// the committed new cells in insertion order.
	std::vector<Cell*> commit_staged();

public:
	Module* mod;
	SigMap* map;
	vector<std::unique_ptr<Wire>> wires_ = {};
	vector<std::unique_ptr<Cell>> cells_ = {};
	TwineChildPool twine_staging;
	dict<RTLIL::Cell*, TwineRef> staged_cell_names_;
	dict<RTLIL::Wire*, TwineRef> staged_wire_names_;
	dict<const std::string*, TwineRef> staged_prefix_cache_;

	void connect(const RTLIL::SigSig &conn);
	void connect(const RTLIL::SigSpec &lhs, const RTLIL::SigSpec &rhs);
	const std::vector<RTLIL::SigSig> &connections() const;

	// Compatible rewrite: root_cell's type has exactly one output port
	// (asserted via kernel/newcelltypes.h). Rewires that output's signal to
	// new_sig, auto-merges src from root_cell + each cell in `extras` (and
	// merge_src_into if set) into every staged new cell and into
	// merge_src_into, then removes root_cell from the module. No input-cone
	// walk: only root_cell is removed.
	void patch(Cell* root_cell, TwineRef old_port, SigSpec new_sig,
			const std::vector<Cell*>& extras = {},
			Cell* merge_src_into = nullptr);

	// Multi-output rewrite: transfer a list of output ports to a list of
	// new sigs. Every entry in `port_replacements` must name an output port
	// of root_cell, and the list must cover ALL of root_cell's output ports
	// (both verified via kernel/newcelltypes.h). For each (port, new_sig)
	// pair the original port signal is connected to new_sig at the module
	// level. All of root_cell's ports are then unset and the cell is
	// removed (asserted: no connections remain at the point of removal).
	// Src is auto-merged from root_cell + extras + merge_src_into into
	// every staged new cell and into merge_src_into.
	void patch_ports(Cell* root_cell,
			const std::vector<std::pair<TwineRef, SigSpec>>& port_replacements,
			const std::vector<Cell*>& extras = {},
			Cell* merge_src_into = nullptr);

	// Flush staged cells_ / wires_ into the module without doing any
	// connect_incremental or port rewiring. Each committed cell's src
	// attribute is pulled from `src_source` (typically the cell that's
	// being expanded / unmapped into the staged helpers, so source-location
	// tracking carries through transparently). Pass nullptr for src_source
	// if the staged helpers have no natural ancestor.
	void commit_inheriting_src(Cell* src_source);

	// Primary overloads: name is a design ref or a twine_staging-local ref.
	RTLIL::Wire *addWire(TwineRef name, int width = 1);
	RTLIL::Wire *addWire(TwineRef name, const RTLIL::Wire *other);
	// Convenience: stages name into twine_staging, then dispatches.
	RTLIL::Wire *addWire(Twine &&name, int width = 1);
	RTLIL::Wire *addWire(Twine &&name, const RTLIL::Wire *other);

	RTLIL::Cell *addCell(TwineRef name, TwineRef type);
	RTLIL::Cell *addCell(TwineRef name, const RTLIL::Cell *other);
	RTLIL::Cell *addCell(Twine &&name, const RTLIL::Cell *other);
	RTLIL::Cell *addCell(Twine &&name, TwineRef type);
	RTLIL::Cell *addCell(TwineRef name, Twine &&type);

	// NEW_ID analog for twine names; see NEW_TWINE in yosys_common.h.
	// Returned refs are twine_staging-local and die at the next commit.
	TwineRef new_name(const std::string *prefix);

	RTLIL::Cell* addDffsr(TwineRef name, const RTLIL::SigSpec &sig_clk, const RTLIL::SigSpec &sig_set, const RTLIL::SigSpec &sig_clr,
		RTLIL::SigSpec sig_d, const RTLIL::SigSpec &sig_q, bool clk_polarity, bool set_polarity, bool clr_polarity, const std::string &src);

	Patch(Module* mod, SigMap* map = nullptr) :
		mod(mod), map(map),
		twine_staging(mod && mod->design ? &mod->design->twines : nullptr) {}
};

YOSYS_NAMESPACE_END

#endif
