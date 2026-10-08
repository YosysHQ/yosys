// NetView: a Netlist built from a uniquified RTLIL design
// - Instances  one per cell, depth first
// - Nets       one per SigMap bit a barrier's A and Y are one net unless
//              either is constant
// - Names      port, then 'keep', then public wire; 'hdlname' gives hdlpath

#ifndef NETVIEW_H
#define NETVIEW_H

#include "kernel/netlist.h"
#include "kernel/rtlil.h"
#include "kernel/sigtools.h"

#include <array>
#include <deque>
#include <map>
#include <string_view>
#include <tuple>
#include <unordered_map>

YOSYS_NAMESPACE_BEGIN

namespace detail {

// Buildability
RTLIL::Module *childModule(RTLIL::Design *design, const RTLIL::Cell *cell);
bool checkUniquified(RTLIL::Design *design, RTLIL::Module *top, RTLIL::Module *module, pool<RTLIL::Module *> &seen, std::string &reason);

// Cells
bool internalType(RTLIL::IdString type);
void addBarrierAliases(RTLIL::Module *module, SigMap &sigmap);

// Port shapes
Netlist::Dir portDir(bool input, bool output);
Netlist::PortShape wireShape(RTLIL::Wire *wire);
void moduleShapes(RTLIL::Module *module, std::vector<Netlist::PortShape> &out);
bool libraryPorts(const RTLIL::Cell *cell, std::vector<Netlist::PortShape> &out);
Netlist::Dir libraryPortDir(const RTLIL::Cell *cell, RTLIL::IdString port, bool internal);

// Names
std::string plainName(RTLIL::IdString id);
RTLIL::IdString escapedPortId(const RTLIL::Cell *cell, const RTLIL::Module *sub, const std::string &name);
bool isVector(const RTLIL::Wire *wire);
std::vector<std::string> hdlPath(const RTLIL::AttrObject *object);
Netlist::NetName netName(const RTLIL::SigBit &bit);
// Net name preference, smaller is better
using NameRank = std::tuple<bool, bool, bool, size_t, std::string_view, int>;
NameRank nameRank(const RTLIL::SigBit &bit);
uint64_t bitKey(const RTLIL::SigBit &bit);

} // namespace detail

struct NetView final : public Netlist
{
	NetView() = default;
	NetView(const NetView &) = delete;
	NetView &operator=(const NetView &) = delete;

	void build(RTLIL::Design *design, PortModel *ports = nullptr);
	static bool buildable(RTLIL::Design *design, std::string &reason);
	void reset();
	bool built() const;
	static RTLIL::Module *topModule(RTLIL::Design *design);

	bool valid() const override;

	Instance *top() const override;
	bool hostPorts(const Instance *inst, std::vector<PortShape> &out) const override;

	const std::vector<Net *> &nets(const Instance *scope) const override;
	Net *constNet(const Instance *scope, bool one) const override;
	NetName wireName(const Net *net) const override;
	const std::vector<Alias> &aliases(const Instance *scope) const override;

	// RTLIL correspondence
	RTLIL::Cell *cell(const Instance *inst) const;
	Instance *instance(const RTLIL::Cell *cell) const;
	RTLIL::Module *module(const Instance *scope) const;
	Instance *scope(const RTLIL::Module *module) const;
private:
	using PortShapes = std::vector<PortShape>;
	using Nets = std::vector<Net *>;
	using Aliases = std::vector<Alias>;
	using ConstNets = std::array<Net *, 2>; // tie-low, tie-high

	void buildTop(RTLIL::Module *top);
	Instance *newInstance(RTLIL::Cell *cell, RTLIL::Module *module, Instance *parent);
	void buildScope(RTLIL::Module *module, Instance *scope);
	void makePins(Instance *inst);
	const PortShapes *portsFor(Instance *inst, RTLIL::Module *sub);
	Pin *makePin(Instance *inst, uint32_t port, int bit, Net *net);
	void makeTerm(Pin *pin, Net *inner_net);
	Net *newNet(Instance *scope, const RTLIL::SigBit &bit);
	void registerAliases(RTLIL::Module *module, Instance *scope);
	void setNameBit(Net *net, const RTLIL::SigBit &bit);
	RTLIL::SigBit nameBit(const Net *net) const;
	SigMap &sigmapFor(RTLIL::Module *module) const;
	Net *knownNet(const RTLIL::SigBit &bit) const;
	Net *findOrMakeNet(RTLIL::Module *module, const RTLIL::SigBit &bit);
private:
	RTLIL::Design *design_ = nullptr;
	PortModel *ports_ = nullptr;
	Instance *top_ = nullptr;

	// Records
	std::deque<Instance> instances_;
	std::deque<Pin> pins_;
	std::deque<Net> nets_;
	std::deque<Term> terms_;
	uint32_t next_inst_id_ = 1; // 0 is the top
	uint32_t next_pin_id_ = 1;
	uint32_t next_net_id_ = 1;
	uint32_t next_term_id_ = 1;

	// Port shapes
	std::deque<PortShapes> shape_store_;
	dict<std::string, const PortShapes *> shape_cache_; // library leaf types

	// Scope contents
	std::unordered_map<const Instance *, Nets> scope_nets_;
	std::unordered_map<const Instance *, Aliases> scope_aliases_;
	std::unordered_map<const Instance *, ConstNets> const_nets_;

	// RTLIL to records
	dict<uint32_t, Instance *> cell_inst_; // by cell hashidx_
	IdMap<RTLIL::Cell *> inst_cell_;
	dict<const RTLIL::Module *, Instance *> module_scope_;
	IdMap<RTLIL::Module *> inst_module_;

	// Nets by bit
	mutable std::map<RTLIL::Module *, SigMap> sigmaps_;
	dict<uint64_t, Net *> bit_net_;
	IdMap<RTLIL::SigBit> net_bit_;
	IdMap<RTLIL::SigBit> net_name_bit_; // naming bit when it differs
	IdMap<NetName> net_names_;
};

YOSYS_NAMESPACE_END

#endif
