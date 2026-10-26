// NetView: a Netlist built from an RTLIL design
// - Instances  one per cell occurrence, depth first in statement order
// - Nets       one per SigMap bit a barrier's A and Y are one net unless
//              either is constant
// - Names      port, then 'keep', then public wire. 'hdlname' gives hdlpath

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

// A list of values per key, empty for a missing key
template <typename K, typename V> struct ListMap {
	void add(const K &key, V value) { data[key].push_back(value); }
	const std::vector<V> &get(const K &key) const
	{
		auto it = data.find(key);
		if (it != data.end())
			return it->second;
		return none;
	}
	void clear() { data.clear(); }
	dict<K, std::vector<V>> data;
	std::vector<V> none;
};

namespace detail {

struct Fingerprint;
uint64_t mix64(uint64_t state, uint64_t value);
bool designAlive(const RTLIL::Design *design);

// Buildability
RTLIL::Module *childModule(RTLIL::Design *design, const RTLIL::Cell *cell);
uint64_t countInstances(RTLIL::Design *design, RTLIL::Module *module, dict<RTLIL::Module *, uint64_t> &counts);
bool checkHierarchy(RTLIL::Design *design, RTLIL::Module *module, pool<RTLIL::Module *> &used, pool<RTLIL::Module *> &open, std::string &reason);
bool checkModule(RTLIL::Module *module, std::string &reason);
bool indicesFitInt(const RTLIL::Wire *wire);
bool checkIndices(RTLIL::Module *module, std::string &reason);
void addUsedBlackboxes(RTLIL::Design *design, RTLIL::Module *module, pool<RTLIL::Module *> &blackboxes);

// Cells
bool isInternalType(RTLIL::IdString type);
bool isTransparentType(RTLIL::IdString type);
void addConnectAliases(RTLIL::Module *module, SigMap &sigmap);
void addBarrierAliases(RTLIL::Module *module, SigMap &sigmap);
std::vector<RTLIL::Cell *> statementOrder(RTLIL::Module *module);

// Port shapes
// The host table that knows a cell type
enum class CellTypeTable : uint8_t {
	Static,
	Yosys
};
Netlist::PortShape wireShape(RTLIL::Wire *wire);
void moduleShapes(RTLIL::Module *module, std::vector<Netlist::PortShape> &out);
bool cellTypePortShapes(const RTLIL::Cell *cell, std::vector<Netlist::PortShape> &out);
Netlist::Dir cellTypePortDir(const RTLIL::Cell *cell, RTLIL::IdString port, CellTypeTable table);

// Names
std::string unescapedName(RTLIL::PooledName id);
RTLIL::IdString escapedPortId(const RTLIL::Design *design, const RTLIL::Cell *cell, const RTLIL::Module *sub, const std::string &name);
bool isVector(const RTLIL::Wire *wire);
std::vector<std::string> sourcePath(const RTLIL::AttrObject *object, std::string_view name);
std::vector<std::string> flattenPath(std::string_view name);
size_t flattenSeparator(std::string_view name);
Netlist::NetName netName(const RTLIL::SigBit &bit);
// Net name preference, smaller is better
using NetNameRank = std::tuple<bool, bool, bool, size_t, std::string, int>;
NetNameRank netNameRank(const RTLIL::SigBit &bit);
uint64_t bitKey(const RTLIL::SigBit &bit);

// Fingerprint
void hashDesign(Fingerprint &fp, RTLIL::Design *design);
void hashModule(Fingerprint &fp, RTLIL::Module *module);
void hashWire(Fingerprint &fp, RTLIL::Wire *wire);
void hashCell(Fingerprint &fp, RTLIL::Cell *cell);

// The records and their next ids
struct RecordStore {
	std::deque<Netlist::Instance> instances;
	std::deque<Netlist::Pin> pins;
	std::deque<Netlist::Net> nets;
	std::deque<Netlist::Term> terms;
	uint32_t next_inst_id = 0; // the top comes first and takes 0
	uint32_t next_pin_id = 1;
	uint32_t next_net_id = 1;
	uint32_t next_term_id = 1;
	Netlist::Instance *newInstance();
	Netlist::Pin *newPin();
	Netlist::Net *newNet();
	Netlist::Term *newTerm();
	void clear();
};

struct PortShapeCache {
	std::deque<std::vector<Netlist::PortShape>> shape_store;
	dict<std::string, const std::vector<Netlist::PortShape> *> shapes_by_leaf_type; // library leaf types
	pool<std::string> unmodeled_leaf_types; // leaf types that the model does not know
	void clear();
};

struct InstanceRtlil {
	RTLIL::Cell *cell = nullptr;     // none for the top
	RTLIL::Module *module = nullptr; // none for leaves
};

struct NetRtlil {
	RTLIL::SigBit bit; // canonical SigMap bit
	RTLIL::SigBit name_bit;
	Netlist::NetName name; // copied out of RTLIL
};

struct NetsByScopeBit {
	Netlist::Net *get(const Netlist::Instance *scope, const RTLIL::SigBit &bit) const;
	void set(const Netlist::Instance *scope, const RTLIL::SigBit &bit, Netlist::Net *net);
	void clear();
	dict<std::pair<uint32_t, uint64_t>, Netlist::Net *> data;
};

struct RtlilIndex {
	ListMap<uint32_t, Netlist::Instance *> instances_by_cell; // by cell hashidx_
	ListMap<const RTLIL::Module *, Netlist::Instance *> scopes_by_module;
	IdMap<InstanceRtlil> instance_rtlil;
	IdMap<NetRtlil> net_rtlil;
	NetsByScopeBit nets_by_scope_bit;
	void clear();
};

class ChangeDetector {
public:
	void arm(RTLIL::Design *design, std::vector<std::string> module_names);
	void noteEvent();
	bool isStale(RTLIL::Design *design) const;
	void clear();
private:
	uint64_t computeFingerprint(RTLIL::Design *design) const;

	uint64_t fingerprint_ = 0;
	std::vector<std::string> tracked_module_names_; // modules with a scope
	mutable bool maybe_changed_ = false;
	mutable bool stale_ = false;
};

} // namespace detail

struct NetView final : public Netlist, public RTLIL::Monitor
{
	using PortShapes = std::vector<PortShape>;

	NetView() = default;
	~NetView() override;
	NetView(const NetView &) = delete;
	NetView &operator=(const NetView &) = delete;

	void build(RTLIL::Design *design, PortModel *ports = nullptr);
	static bool buildable(RTLIL::Design *design, std::string &reason);
	void reset();
	std::unique_ptr<NetView> retire();
	bool built() const;
	static RTLIL::Module *topModule(RTLIL::Design *design);

	// Call invalidateCheck() when the design may have changed: edits without a
	// Monitor event (e.g. opt_clean) are not seen otherwise
	bool valid() const;
	void invalidateCheck();

	Instance *top() const;
	std::array<size_t, 3> counts() const;

	const std::vector<Net *> &nets(const Instance *scope) const;
	std::vector<Net *> constNets(Net::Const value) const;
	NetName wireName(const Net *net) const;
	const std::vector<NetAlias> &aliases(const Instance *scope) const;

	// RTLIL correspondence
	RTLIL::Cell *cell(const Instance *inst) const;
	Instance *instance(const RTLIL::Cell *cell, const Instance *scope = nullptr) const;
	RTLIL::Module *module(const Instance *scope) const;
	const std::vector<Instance *> &scopes(const RTLIL::Module *module) const;

	// RTLIL::Monitor: every event marks the view for a re-check
	void notify_module_add(RTLIL::Module *module) override;
	void notify_module_del(RTLIL::Module *module) override;
	void notify_connect(RTLIL::Cell *cell, RTLIL::IdString port, const RTLIL::SigSpec &old_sig, const RTLIL::SigSpec &new_sig) override;
	void notify_connect(RTLIL::Module *module, const RTLIL::SigSig &conn) override;
	void notify_connect(RTLIL::Module *module, const std::vector<RTLIL::SigSig> &conns) override;
	void notify_blackout(RTLIL::Module *module) override;
private:
	struct ScopeContents {
		std::vector<Net *> nets;
		std::vector<NetAlias> aliases;
		Net *zero_net = nullptr;
		Net *one_net = nullptr;
		Net *tieNet(Net::Const value) const;
		void setTieNet(Net::Const value, Net *net);
	};

	void unregisterMonitor();
	void clearTables();
	void buildTop(RTLIL::Module *top);
	// Ports of an instance's master as the host knows them, ignoring PortModel
	bool hostPortShapes(const Instance *inst, std::vector<PortShape> &out) const;
	const PortShapes *portShapesFor(Instance *inst, RTLIL::Module *sub);
	Instance *newInstance(RTLIL::Cell *cell, RTLIL::Module *module, Instance *parent);
	void buildScope(RTLIL::Module *module, Instance *scope);
	void makePins(Instance *inst);
	Pin *makePin(Instance *inst, uint32_t port, int bit, Net *net);
	void makeTerm(Pin *pin, Net *inner_net);
	Net *newNet(Instance *scope, const RTLIL::SigBit &bit);
	void registerAliases(RTLIL::Module *module, Instance *scope);
	void setNameBit(Net *net, const RTLIL::SigBit &bit);
	RTLIL::SigBit nameBit(const Net *net) const;
	SigMap &sigmapFor(RTLIL::Module *module);
	Net *findOrMakeNet(Instance *scope, const RTLIL::SigBit &bit);
	Net *findOrMakeTieNet(Instance *scope, const RTLIL::SigBit &canon);
	const ScopeContents &scopeContents(const Instance *scope) const;

	RTLIL::Design *design_ = nullptr;
	PortModel *ports_ = nullptr;
	Instance *top_ = nullptr;
	detail::RecordStore records_;
	detail::PortShapeCache shapes_;
	detail::RtlilIndex index_;
	std::unordered_map<const Instance *, ScopeContents> scope_contents_;
	detail::ChangeDetector watch_;
	std::map<RTLIL::Module *, SigMap> sigmaps_;
};

YOSYS_NAMESPACE_END

#endif
