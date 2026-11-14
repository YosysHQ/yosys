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
RTLIL::Module *topModule(RTLIL::Design *design);
RTLIL::Module *childModule(RTLIL::Design *design, const RTLIL::Cell *cell);
// the hdlname of a module or scope cell, else its name
// a uniquified module keeps its original name in hdlname, flatten names a scope that way
template <typename T> std::string hdlName(const T *object)
{
	return object->has_attribute(ID::hdlname) ? object->get_string_attribute(ID::hdlname) : object->name.unescape();
}

using RecordCounts = dict<RTLIL::Module *, uint64_t>;
// a blackbox is a leaf, its body has no records
enum class ModuleRole : uint8_t { Leaf, Scope };
bool countRecords(RTLIL::Module *module, ModuleRole role, RecordCounts &counts, std::string &reason);
bool countBody(RTLIL::Module *module, RecordCounts &counts, std::string &reason, uint64_t &count);

constexpr std::string_view owned_marker_prefix = "\\netview_"; // netview_<attr> marks an attr the tracker set
constexpr std::string_view cut_attr = "\\netview_cut";
void addConnectAliases(RTLIL::Module *module, SigMap &sigmap);
std::vector<RTLIL::Cell *> statementOrder(RTLIL::Module *module);
std::string ownedMarkerName(RTLIL::Design *design, RTLIL::IdString attr);

void modulePorts(RTLIL::Module *module, std::vector<Netlist::Port> &out);
bool cellTypePorts(const RTLIL::Cell *cell, std::vector<Netlist::Port> &out);

using NetNameRank = std::tuple<bool, bool, std::string, int>;
RTLIL::IdString escapedPortId(RTLIL::Design *design, const Netlist::Instance *inst, const std::string &name);
bool isVector(const RTLIL::Wire *wire);
NetNameRank netNameRank(const RTLIL::SigBit &bit);

// the nets that ports join with a net, over the hierarchy
std::vector<const Netlist::Net *> connectedNets(const Netlist::Net *net);

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
	Netlist::Instance *newInstance(RTLIL::Cell *cell, RTLIL::Module *module, Netlist::Instance *parent);
	void buildScope(Netlist::Instance *scope);
	void makePins(Netlist::Instance *inst);
	const Netlist::CellType *typeOf(const RTLIL::Cell *cell, RTLIL::Module *module);
	bool leafPorts(const RTLIL::Cell *cell, Netlist::CellType &type);
	void nameNets(Netlist::Instance *scope);
	void setNameBit(Netlist::Net *net, const RTLIL::SigBit &bit);
	SigMap &sigmapFor(RTLIL::Module *module);
	void addBarrierAliases(RTLIL::Module *module, SigMap &sigmap) const;
	Netlist::Net *findOrMakeNet(Netlist::Instance *scope, const RTLIL::SigBit &bit);
	NetView &view_;
	Netlist::CellLibrary *library_;
	dict<std::pair<uint32_t, RTLIL::SigBit>, Netlist::Net *> nets_by_scope_bit_; // by scope id and canonical bit
	dict<RTLIL::IdString, const Netlist::CellType *> shared_types_;
	BodyKeys body_keys_;
	pool<std::string> types_not_in_library_;
	std::map<RTLIL::Module *, SigMap> sigmaps_;
};

} // namespace detail

YOSYS_NAMESPACE_END

#endif
