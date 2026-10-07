// NetView: a Netlist built from an RTLIL design
// - Instances  one per cell, depth first

#ifndef NETVIEW_H
#define NETVIEW_H

#include "kernel/netlist.h"
#include "kernel/rtlil.h"

#include <deque>

YOSYS_NAMESPACE_BEGIN

namespace detail {

// Buildability
RTLIL::Module *childModule(RTLIL::Design *design, const RTLIL::Cell *cell);

} // namespace detail

struct NetView final : public Netlist
{
	NetView() = default;
	NetView(const NetView &) = delete;
	NetView &operator=(const NetView &) = delete;

	void build(RTLIL::Design *design);
	void reset();
	bool built() const;
	static RTLIL::Module *topModule(RTLIL::Design *design);

	bool valid() const override;

	Instance *top() const override;

	// RTLIL correspondence
	RTLIL::Cell *cell(const Instance *inst) const;
	Instance *instance(const RTLIL::Cell *cell) const;
	RTLIL::Module *module(const Instance *scope) const;
	Instance *scope(const RTLIL::Module *module) const;
private:
	void buildTop(RTLIL::Module *top);
	Instance *newInstance(RTLIL::Cell *cell, RTLIL::Module *module, Instance *parent);
	void buildScope(RTLIL::Module *module, Instance *scope);
private:
	RTLIL::Design *design_ = nullptr;
	Instance *top_ = nullptr;

	// Records
	std::deque<Instance> instances_;
	uint32_t next_inst_id_ = 1; // 0 is the top

	// RTLIL to records
	dict<uint32_t, Instance *> cell_inst_; // by cell hashidx_
	IdMap<RTLIL::Cell *> inst_cell_;
	dict<const RTLIL::Module *, Instance *> module_scope_;
	IdMap<RTLIL::Module *> inst_module_;
};

YOSYS_NAMESPACE_END

#endif
