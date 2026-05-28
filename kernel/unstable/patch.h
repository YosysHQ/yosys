#ifndef PATCH_H
#define PATCH_H

#include "kernel/rtlil.h"
#include "kernel/sigtools.h"

YOSYS_NAMESPACE_BEGIN

struct RTLIL::Patch final : public CellAdderMixin<RTLIL::Patch>
{
private:
	void gc(Cell* old_cell);

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
	vector<std::unique_ptr<Wire>> wires_ = {};
	vector<std::unique_ptr<Cell>> cells_ = {};

	void connect(const RTLIL::SigSig &conn);
	void connect(const RTLIL::SigSpec &lhs, const RTLIL::SigSpec &rhs);
	const std::vector<RTLIL::SigSig> &connections() const;

	void patch(Cell* old_cell, IdString old_port, SigSpec new_sig);
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
