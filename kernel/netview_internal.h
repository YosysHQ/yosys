#ifndef NETVIEW_INTERNAL_H
#define NETVIEW_INTERNAL_H

#include "kernel/netview.h"
#include "kernel/sigtools.h"

#include <map>
#include <string_view>
#include <tuple>

YOSYS_NAMESPACE_BEGIN

namespace detail
{

struct Fingerprint;
RTLIL::IdString escapedPortId(RTLIL::Design *design, const Netlist::Instance *inst, const std::string &name);
bool isVector(const RTLIL::Wire *wire);
void modulePorts(RTLIL::Module *module, std::vector<Netlist::Port> &out);
bool cellTypePorts(const RTLIL::Cell *cell, std::vector<Netlist::Port> &out);
RTLIL::Module *topModule(RTLIL::Design *design);
RTLIL::Module *childModule(RTLIL::Design *design, const RTLIL::Cell *cell);
std::string flattenNames(const std::string &name);
// uniquify keeps the original module name in hdlname, flatten names a scope that way
template <typename T> std::string hdlName(const T *object)
{
	if (object->has_attribute(ID::hdlname))
		return object->get_string_attribute(ID::hdlname);
	return flattenNames(object->name.unescape());
}

using RecordCounts = dict<RTLIL::Module *, uint64_t>;
enum class ModuleRole : uint8_t {
	Leaf, // blackbox, its body has no records
	Scope
};
bool countRecords(RTLIL::Module *module, ModuleRole role, RecordCounts &counts, std::string &reason);
bool countBody(RTLIL::Module *module, RecordCounts &counts, std::string &reason, uint64_t &count);

std::vector<RTLIL::Cell *> statementOrder(RTLIL::Module *module);
using NetNameRank = std::tuple<bool, bool, std::string, int>;
NetNameRank netNameRank(const RTLIL::SigBit &bit);
constexpr std::string_view owned_marker_prefix = "\\netview_"; // netview_<attr> marks an attr the tracker set
constexpr std::string_view cut_attr = "\\netview_cut";
std::string ownedMarkerName(RTLIL::Design *design, RTLIL::IdString attr);
void addConnectAliases(RTLIL::Module *module, SigMap &sigmap);
Netlist::NetList connectedNets(const Netlist::Net *net);

using BodyKeys = dict<RTLIL::IdString, uint64_t>; // by module name
uint64_t bodyKey(RTLIL::Module *module, BodyKeys &keys);
uint64_t designModuleHash(RTLIL::Module *module);
void hashModule(Fingerprint &fp, RTLIL::Module *module);
uint64_t wireHash(RTLIL::Wire *wire, const BodyKeys *body_keys = nullptr);
uint64_t cellHash(RTLIL::Cell *cell, const BodyKeys *body_keys = nullptr);
uint64_t designFingerprint(RTLIL::Design *design, const std::vector<std::string> &module_names);

struct ViewBuilder {
	ViewBuilder(NetView &view, Netlist::CellLibrary *library);
	void build(RTLIL::Module *top);
private:
	const Netlist::CellType *typeOf(const RTLIL::Cell *cell, RTLIL::Module *module);
	bool leafPorts(const RTLIL::Cell *cell, Netlist::CellType &type);
	Netlist::Instance *newInstance(RTLIL::Cell *cell, RTLIL::Module *module, Netlist::Instance *parent);
	void buildScope(Netlist::Instance *scope);
	void makePins(Netlist::Instance *inst);
	Netlist::Pin *newPin(Netlist::Instance *inst, uint32_t port_index, int bit, Netlist::Net *net);
	void nameNets(Netlist::Instance *scope);
	SigMap &sigmapFor(RTLIL::Module *module);
	void addBarrierAliases(RTLIL::Module *module, SigMap &sigmap) const;
	void setNameBit(Netlist::Net *net, const RTLIL::SigBit &bit);
	Netlist::Net *findOrMakeNet(Netlist::Instance *scope, const RTLIL::SigBit &bit);
	NetView &view_;
	Netlist::CellLibrary *library_;
	using BitInScopeId = std::pair<uint32_t, RTLIL::SigBit>; // scope id and canonical bit
	dict<BitInScopeId, Netlist::Net *> nets_by_scope_bit_;
	dict<RTLIL::IdString, const Netlist::CellType *> shared_types_;
	BodyKeys body_keys_;
	pool<std::string> types_not_in_library_;
	std::map<RTLIL::Module *, SigMap> sigmaps_;
};

} // namespace detail

YOSYS_NAMESPACE_END

#endif
