// NetView: a Netlist built from a uniquified RTLIL design
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
bool checkUniquified(RTLIL::Design *design, RTLIL::Module *top, RTLIL::Module *module, pool<RTLIL::Module *> &seen, std::string &reason);

// Cells
bool internalType(RTLIL::IdString type);

// Port shapes
Netlist::Dir portDir(bool input, bool output);
Netlist::PortShape wireShape(RTLIL::Wire *wire);
void moduleShapes(RTLIL::Module *module, std::vector<Netlist::PortShape> &out);
bool libraryPorts(const RTLIL::Cell *cell, std::vector<Netlist::PortShape> &out);
Netlist::Dir libraryPortDir(const RTLIL::Cell *cell, RTLIL::IdString port, bool internal);

} // namespace detail

struct NetView final : public Netlist
{
	NetView() = default;
	NetView(const NetView &) = delete;
	NetView &operator=(const NetView &) = delete;

	void build(RTLIL::Design *design);
	static bool buildable(RTLIL::Design *design, std::string &reason);
	void reset();
	bool built() const;
	static RTLIL::Module *topModule(RTLIL::Design *design);

	bool valid() const override;

	Instance *top() const override;
	bool hostPorts(const Instance *inst, std::vector<PortShape> &out) const override;

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
