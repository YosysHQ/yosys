#ifndef PATCH_H
#define PATCH_H

#include "kernel/rtlil.h"
#include "kernel/sigtools.h"

YOSYS_NAMESPACE_BEGIN

struct RTLIL::Patch final : public CellAdderMixin<RTLIL::Patch>
{
	Hasher::hash_t hashidx_;
	[[nodiscard]] Hasher hash_into(Hasher h) const { h.eat(hashidx_); return h; }

protected:
	void add(RTLIL::Wire *wire);
	void add(RTLIL::Cell *cell);
	void add(RTLIL::Process *process);

public:
	Module *mod;
	SigMap map;
	vector<Wire> wires_;
	vector<Cell> cells_;

	vector<RTLIL::SigSig> connections_;

	void connect(const RTLIL::SigSig &conn);
	void connect(const RTLIL::SigSpec &lhs, const RTLIL::SigSpec &rhs);
	const std::vector<RTLIL::SigSig> &connections() const;

	void patch();
	RTLIL::Wire *addWire(RTLIL::IdString name, int width = 1);
	RTLIL::Wire *addWire(RTLIL::IdString name, const RTLIL::Wire *other);

	RTLIL::Cell *addCell(RTLIL::IdString name, RTLIL::IdString type);
	RTLIL::Cell *addCell(RTLIL::IdString name, const RTLIL::Cell *other);

	RTLIL::Cell* addDffsr(RTLIL::IdString name, const RTLIL::SigSpec &sig_clk, const RTLIL::SigSpec &sig_set, const RTLIL::SigSpec &sig_clr,
		RTLIL::SigSpec sig_d, const RTLIL::SigSpec &sig_q, bool clk_polarity, bool set_polarity, bool clr_polarity, const std::string &src);
};

YOSYS_NAMESPACE_END

#endif
