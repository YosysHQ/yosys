#ifndef NETVIEW_INTERNAL_H
#define NETVIEW_INTERNAL_H

#include "kernel/netview.h"
#include "kernel/sigtools.h"

#include <deque>
#include <map>
#include <string_view>
#include <tuple>

YOSYS_NAMESPACE_BEGIN

namespace detail
{

template <typename K, typename V> struct ListMap {
	void add(const K &key, V value) { data[key].push_back(value); }
	const std::vector<V> &get(const K &key) const { return data.at(key, none); }
	void clear() { data.clear(); }
	dict<K, std::vector<V>> data;
	std::vector<V> none;
};

template <typename T> T *recordAt(std::deque<T> &records, uint32_t at)
{
	if (at < records.size())
		return &records[at];
	return nullptr;
}

struct Fingerprint;
bool designAlive(const RTLIL::Design *design);
RTLIL::Module *topModule(RTLIL::Design *design);

// Buildability
RTLIL::Module *childModule(RTLIL::Design *design, const RTLIL::Cell *cell);

NetView::Counts countRecords(RTLIL::Design *design, RTLIL::Module *module, dict<RTLIL::Module *, NetView::Counts> &counts);
uint64_t portBits(RTLIL::Module *module);
uint64_t wireBits(RTLIL::Module *module);
uint64_t cellPinBits(RTLIL::Design *design, const RTLIL::Cell *cell);
bool checkHierarchy(RTLIL::Design *design, RTLIL::Module *module, pool<RTLIL::Module *> &used, pool<RTLIL::Module *> &open, std::string &reason);
bool checkModule(RTLIL::Design *design, RTLIL::Module *module, pool<RTLIL::Module *> &blackboxes, std::string &reason);
bool checkIndices(RTLIL::Module *module, std::string &reason);

// Cells
bool isInternalType(RTLIL::IdString type);
bool isTransparentType(RTLIL::IdString type);
void addConnectAliases(RTLIL::Module *module, SigMap &sigmap);
std::vector<RTLIL::Cell *> statementOrder(RTLIL::Module *module);

// Ports
Netlist::Port wirePort(RTLIL::Wire *wire);
void modulePorts(RTLIL::Module *module, std::vector<Netlist::Port> &out);
bool cellTypePorts(const RTLIL::Cell *cell, std::vector<Netlist::Port> &out);
Netlist::PortDir cellTypePortDir(const RTLIL::Cell *cell, RTLIL::IdString port, bool static_type);

// Names
using NetNameRank = std::tuple<bool, bool, bool, size_t, std::string, int>;

enum class WireOrigin : uint8_t {
	Declared,
	SplitFromVector // splitnets made it of a vector bit
};

std::string unescapedName(RTLIL::PooledName id);
RTLIL::IdString escapedPortId(const RTLIL::Design *design, const RTLIL::Cell *cell, const RTLIL::Module *sub, const std::string &name);
bool isVector(const RTLIL::Wire *wire);
std::vector<std::string> sourcePath(const RTLIL::AttrObject *object, std::string_view name);
std::vector<std::string> flattenPath(std::string_view name);
size_t flattenSeparator(std::string_view name);
bool trailingIndex(std::string_view name, int &index);
Netlist::NetName netName(const RTLIL::SigBit &bit, WireOrigin origin);
NetNameRank netNameRank(const RTLIL::SigBit &bit);
uint64_t bitKey(const RTLIL::SigBit &bit);
void nameChildren(Netlist::Instance *scope);

// Body keys
uint64_t pinHash(char tag, const std::string &child, const NetView &view, const Netlist::Pin *pin, const Netlist::Net *net);
void eatNet(Fingerprint &fp, const NetView &view, const Netlist::Net *net);

// Walks
bool pinMatchesTarget(const Netlist::Pin *pin, Netlist::WalkTarget target);
void addLeafPins(const Netlist::Net *net, Netlist::WalkTarget target, std::vector<Netlist::Pin *> &out);

// Fingerprint
void hashDesign(Fingerprint &fp, RTLIL::Design *design);
void hashModule(Fingerprint &fp, RTLIL::Module *module);
void hashWire(Fingerprint &fp, RTLIL::Wire *wire);
void hashCell(Fingerprint &fp, RTLIL::Cell *cell);
uint64_t designFingerprint(RTLIL::Design *design, const std::vector<std::string> &module_names);

struct RecordStore {
	std::deque<Netlist::Instance> instances;
	std::deque<Netlist::Pin> pins;
	std::deque<Netlist::Net> nets;
	uint32_t next_inst_id = 0;
	uint32_t next_pin_id = 1;
	uint32_t next_net_id = 1;

      public:
	Netlist::Instance *newInstance();
	Netlist::Pin *newPin();
	Netlist::Net *newNet();
};

// The port lists of the instances
struct PortStore {
	std::deque<std::vector<Netlist::Port>> lists;
	dict<std::string, const std::vector<Netlist::Port> *> lists_by_library_type;
	pool<std::string> types_not_in_library;
};

struct InstanceRtlil {
	RTLIL::Cell *cell = nullptr;	 // none for the top
	RTLIL::Module *module = nullptr; // none for leaves
};

struct NetRtlil {
	RTLIL::SigBit bit; // canonical SigMap bit
	RTLIL::SigBit name_bit;
	Netlist::NetName name; // copied out of RTLIL
	std::vector<RTLIL::SigBit> wire_bits;
	std::vector<Netlist::NetName> aliases;
};

struct NetsByScopeBit {
	Netlist::Net *get(const Netlist::Instance *scope, const RTLIL::SigBit &bit) const;
	void set(const Netlist::Instance *scope, const RTLIL::SigBit &bit, Netlist::Net *net);

      public:
	dict<std::pair<uint32_t, uint64_t>, Netlist::Net *> data;
};

struct RtlilIndex {
	ListMap<uint32_t, Netlist::Instance *> instances_by_cell; // by cell hashidx_
	ListMap<const RTLIL::Module *, Netlist::Instance *> scopes_by_module;
	Netlist::IdMap<InstanceRtlil> instance_rtlil;
	Netlist::IdMap<NetRtlil> net_rtlil;
	NetsByScopeBit nets_by_scope_bit;
};

struct BodyKeys {
	Netlist::IdMap<uint64_t> keys; // by instance id, 0 if not known
public:
	uint64_t key(const NetView &view, const Netlist::Instance *scope);
};

struct ScopeContents {
	std::vector<Netlist::Net *> nets;
	Netlist::Net *tie_nets[2] = {}; // by value == Const::One
};

struct ViewData {
	RTLIL::Design *design = nullptr;
	Netlist::CellLibrary *library = nullptr;
	Netlist::Instance *top = nullptr;
	RecordStore records;
	PortStore ports;
	RtlilIndex index;
	Netlist::IdMap<ScopeContents> scope_contents; // by scope id
	BodyKeys body_keys; // a cache of NetView::bodyKey
	// the design at the build
	uint64_t fingerprint = 0;
	std::vector<std::string> watched_module_names;
};

struct ViewBuilder {
	ViewBuilder(const NetView &view, ViewData &data);
	void build(RTLIL::Module *top);

      private:
	Netlist::Instance *newInstance(RTLIL::Cell *cell, RTLIL::Module *module, Netlist::Instance *parent);
	void buildScope(RTLIL::Module *module, Netlist::Instance *scope);
	void makePins(Netlist::Instance *inst);
	const std::vector<Netlist::Port> *portsFor(Netlist::Instance *inst, RTLIL::Module *sub);
	bool leafPorts(const Netlist::Instance *inst, std::vector<Netlist::Port> &out);
	Netlist::Pin *makePin(Netlist::Instance *inst, uint32_t port_index, int bit, Netlist::Net *net);
	void setInner(Netlist::Pin *pin, Netlist::Net *inner_net);
	Netlist::Net *newNet(Netlist::Instance *scope, const RTLIL::SigBit &bit);
	void registerWires(RTLIL::Module *module, Netlist::Instance *scope);
	void setNameBit(Netlist::Net *net, const RTLIL::SigBit &bit);
	WireOrigin wireOrigin(const RTLIL::Wire *wire);
	RTLIL::SigBit nameBit(const Netlist::Net *net) const;
	SigMap &sigmapFor(RTLIL::Module *module);
	void addBarrierAliases(RTLIL::Module *module, SigMap &sigmap) const;
	Netlist::Net *findOrMakeNet(Netlist::Instance *scope, const RTLIL::SigBit &bit);
	Netlist::Net *findOrMakeTieNet(Netlist::Instance *scope, const RTLIL::SigBit &canon);

      private:
	const NetView &view_;
	ViewData &data_;
	std::map<RTLIL::Module *, SigMap> sigmaps_;
	std::map<const RTLIL::Module *, dict<std::string, int>> hdlname_counts_; // wires per hdlname
};

} // namespace detail

YOSYS_NAMESPACE_END

#endif
