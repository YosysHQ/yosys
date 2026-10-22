// NetView: a Netlist built from an RTLIL design
// - Instances  one per cell occurrence, depth first in statement order
// - Images     protect barriers marked as image, instances with no module
// - Nets       one per SigMap bit a barrier's A and Y are one net unless
//              either is constant
// - Names      port, then 'keep', then public wire. 'hdlname' gives hdlpath

#ifndef NETVIEW_H
#define NETVIEW_H

#include "kernel/modtools.h"
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

struct Fingerprint;
uint64_t mix64(uint64_t state, uint64_t value);

// Buildability
RTLIL::Module *childModule(RTLIL::Design *design, const RTLIL::Cell *cell);
uint64_t countInstances(RTLIL::Design *design, RTLIL::Module *module, dict<RTLIL::Module *, uint64_t> &counts);
bool checkHierarchy(RTLIL::Design *design, RTLIL::Module *module, pool<RTLIL::Module *> &used, pool<RTLIL::Module *> &open, std::string &reason);
bool checkModule(RTLIL::Module *module, std::string &reason);
bool indicesFitInt(const RTLIL::Wire *wire);
bool checkIndices(RTLIL::Module *module, std::string &reason);
void addUsedBlackboxes(RTLIL::Design *design, RTLIL::Module *module, pool<RTLIL::Module *> &blackboxes);

// Cells
bool internalType(RTLIL::IdString type);
bool transparentType(RTLIL::IdString type);
void addConnectAliases(RTLIL::Module *module, SigMap &sigmap);
std::vector<RTLIL::Cell *> statementOrder(RTLIL::Module *module);

// Port shapes
Netlist::PortShape wireShape(RTLIL::Wire *wire);
void moduleShapes(RTLIL::Module *module, std::vector<Netlist::PortShape> &out);
bool libraryPorts(const RTLIL::Cell *cell, std::vector<Netlist::PortShape> &out);
Netlist::Dir libraryPortDir(const RTLIL::Cell *cell, RTLIL::IdString port, bool internal);

// Names
std::string plainName(RTLIL::PooledName id);
RTLIL::IdString escapedPortId(const RTLIL::Design *design, const RTLIL::Cell *cell, const RTLIL::Module *sub, const std::string &name);
bool isVector(const RTLIL::Wire *wire);
std::vector<std::string> sourcePath(const RTLIL::AttrObject *object, std::string_view name);
std::vector<std::string> flattenPath(std::string_view name);
size_t flattenSeparator(std::string_view name);
Netlist::NetName netName(const RTLIL::SigBit &bit);
// Net name preference, smaller is better
using NameRank = std::tuple<bool, bool, bool, size_t, std::string, int>;
NameRank nameRank(const RTLIL::SigBit &bit);
uint64_t bitKey(const RTLIL::SigBit &bit);

// Fingerprint
void hashDesign(Fingerprint &fp, RTLIL::Design *design);
void hashModule(Fingerprint &fp, RTLIL::Module *module);
void hashWire(Fingerprint &fp, RTLIL::Wire *wire);
void hashCell(Fingerprint &fp, RTLIL::Cell *cell);

// Where an object of a ref was, on a cell or wire
struct Anchor {
	enum class Role : uint8_t {
		Pin,
		Cell,
		Net,
		Barrier // on a $barrier, the pins on its cut side
	};

	// The cut side of a barrier: A at an output pin, Y at an input pin
	enum class Side : uint8_t {
		None,
		A,
		Y
	};

	Role role;
	uint32_t ref;
	std::string scope;      // path, with the own scope of the cell or wire
	std::string port;
	int bit;
	std::string wire_scope; // path of the scope that holds the wire
	bool in_shared_module;
	Side side = Side::None;
};

enum BarrierMark : int {
	MarkCutA = 1,    // the cut wire is on A, at an output
	MarkPortCut = 2, // the cut side holds all uses of a port bit
	MarkImage = 4,   // an instance in the view, keeps a hierarchical pin
};

// An anchor that the rebuilt view holds
struct Hit {
	Anchor anchor;
	const Netlist::Instance *inst; // of a cell anchor
	const Netlist::Net *net;       // of a wire anchor
	bool in_own_scope;
	const RTLIL::Cell *barrier = nullptr; // of a barrier anchor
	const Netlist::Instance *barrier_scope = nullptr;
};

// Anchors
RTLIL::IdString attrId(RTLIL::Design *design, const std::string &name, bool add);
RTLIL::IdString refId(RTLIL::Design *design, bool add);
void markScope(RTLIL::AttrObject *object);
std::vector<const Hit *> pick(const std::vector<Hit> &hits, Anchor::Role role);
std::vector<const void *> unique(std::vector<const void *> objects);

// Barriers
constexpr std::string_view anchor_prefix = "netview_anchor";
RTLIL::Wire *addCutWire(RTLIL::Module *module);
bool isCutWire(const RTLIL::Wire *wire);
int anchorNumber(const RTLIL::Cell *barrier);
std::string barrierScope(const std::string &path, const RTLIL::Cell *barrier);
void markKeep(RTLIL::Design *design, RTLIL::AttrObject *object);
void replaceBit(RTLIL::Module *module, const RTLIL::SigBit &bit, const RTLIL::SigBit &other);
std::vector<const void *> pinsOf(const std::vector<const Netlist::Instance *> &insts, const std::vector<const void *> &leaves);

// Scope paths
std::vector<std::string> ownScope(const RTLIL::AttrObject *object);
std::string joinScope(const std::vector<std::string> &parts);
std::string scopePath(const Netlist::Instance *scope);
std::string withOwnScope(const std::string &path, const RTLIL::AttrObject *object);

} // namespace detail

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

struct NetView final : public Netlist, public RTLIL::Monitor
{
	// The objects of a ref, found again after passes
	struct Found {
		enum class Kind : uint8_t {
			Pin,
			Cell,
			Net,
			Port // of the top, as its pin
		};

		Kind kind;
		Dir hier = Dir::Unknown;  // of a hierarchical pin, Input or Output
		bool image = false;       // protect makes its barrier an image
		bool image_pin = false;
		bool unprotected = false; // moved off a barrier that unprotect removes
		const void *top_pin = nullptr; // of a port by name, set before resolve
		std::vector<const void *> objects = {};
		std::vector<const void *> through_pins = {}; // of a net in its old scope
		bool inside = false; // a hierarchical pin found as its leaf pins inside
		std::vector<const void *> image_a = {}, image_y = {};
		std::vector<const void *> beyond = {}; // the loads beyond its barrier
	};

	NetView() = default;
	~NetView() override;
	NetView(const NetView &) = delete;
	NetView &operator=(const NetView &) = delete;

	void build(RTLIL::Design *design, LeafModel *model = nullptr);
	static bool buildable(RTLIL::Design *design, std::string &reason);
	void reset();
	std::unique_ptr<NetView> retire();
	bool built() const;
	bool isBarrier(const Instance *inst) const;
	static RTLIL::Module *topModule(RTLIL::Design *design);

	// Call invalidateCheck() when the design may have changed: edits without a
	// Monitor event (e.g. opt_clean) are not seen otherwise
	bool valid() const;
	void invalidateCheck();

	void anchor(const std::vector<Found *> &refs);
	void protect(const std::vector<Found *> &refs);
	void clearAnchors(RTLIL::Design *design);
	void resolve(const std::vector<Found *> &refs);
	void innerPins(const Net *net, bool drivers, std::vector<const void *> &found) const;

	Instance *top() const;
	std::array<size_t, 3> counts() const;

	const std::vector<Net *> &nets(const Instance *scope) const;
	std::vector<Net *> constNets(bool one) const;
	NetName wireName(const Net *net) const;
	const std::vector<Alias> &aliases(const Instance *scope) const;

	// RTLIL correspondence
	RTLIL::Cell *cell(const Instance *inst) const;
	Instance *instance(const RTLIL::Cell *cell, const Instance *scope = nullptr) const;
	RTLIL::Module *module(const Instance *scope) const;
	const std::vector<Instance *> &scopes(const RTLIL::Module *module) const;
	const std::vector<RTLIL::SigBit> &wireBits(const Net *net) const;

	// RTLIL::Monitor: every event marks the view for a re-check
	void notify_module_add(RTLIL::Module *module) override;
	void notify_module_del(RTLIL::Module *module) override;
	void notify_connect(RTLIL::Cell *cell, RTLIL::IdString port, const RTLIL::SigSpec &old_sig, const RTLIL::SigSpec &new_sig) override;
	void notify_connect(RTLIL::Module *module, const RTLIL::SigSig &conn) override;
	void notify_connect(RTLIL::Module *module, const std::vector<RTLIL::SigSig> &conns) override;
	void notify_blackout(RTLIL::Module *module) override;
private:
	using PortShapes = std::vector<PortShape>;

	struct ScopeData {
		std::vector<Net *> nets;
		std::vector<Alias> aliases;
		std::array<Net *, 2> consts = {}; // tie-low, tie-high
	};

	struct InstData {
		RTLIL::Cell *cell = nullptr;     // none for the top
		RTLIL::Module *module = nullptr; // none for leaves
	};

	struct NetData {
		RTLIL::SigBit bit;      // canonical SigMap bit
		RTLIL::SigBit name_bit;
		NetName name;           // copied out of RTLIL
		std::vector<RTLIL::SigBit> wire_bits;
	};

	struct NetsByScopeBit {
		Net *get(const Instance *scope, const RTLIL::SigBit &bit) const;
		void set(const Instance *scope, const RTLIL::SigBit &bit, Net *net);
		void clear() { data.clear(); }
		dict<std::pair<uint32_t, uint64_t>, Net *> data;
	};

	void clearTables();
	void buildTop(RTLIL::Module *top);
	Instance *newInstance(RTLIL::Cell *cell, RTLIL::Module *module, Instance *parent);
	void buildScope(RTLIL::Module *module, Instance *scope);
	void makePins(Instance *inst);
	void addBarrierScope(RTLIL::Cell *cell, Instance *scope);
	Net *newInnerNet(Instance *scope, int bit, bool scalar);
	// Ports of an instance's master as the host knows them, ignoring LeafModel
	bool hostPorts(const Instance *inst, std::vector<PortShape> &out) const;
	const PortShapes *portsFor(Instance *inst, RTLIL::Module *sub);
	Pin *makePin(Instance *inst, uint32_t port, int bit, Net *net);
	void makeTerm(Pin *pin, Net *inner_net);
	Net *newNet(Instance *scope, const RTLIL::SigBit &bit);
	void registerWires(RTLIL::Module *module, Instance *scope);
	void setNameBit(Net *net, const RTLIL::SigBit &bit);
	RTLIL::SigBit nameBit(const Net *net) const;
	SigMap &sigmapFor(RTLIL::Module *module);
	void addBarrierAliases(RTLIL::Module *module, SigMap &sigmap) const;
	const ScopeData &scopeData(const Instance *scope) const;
	Net *findOrMakeNet(Instance *scope, const RTLIL::SigBit &bit);

	bool designAlive() const;
	void unregisterMonitor();
	uint64_t fingerprint() const;

	// Anchors: barriers
	RTLIL::Cell *addBarrier(RTLIL::Module *module, const RTLIL::SigBit &a, const RTLIL::SigBit &y);
	bool hasMark(const RTLIL::Cell *barrier, int mark) const;
	RTLIL::Cell *cutPin(const Pin *pin);
	void anchorBarrier(const Pin *pin, uint32_t ref);
	void addBarrierAnchor(RTLIL::Cell *barrier, const std::string &path, detail::Anchor anchor);
	void protectLeafPin(const Pin *pin, uint32_t ref);
	void isolateCell(const Instance *inst);
	bool onSide(const Pin *pin, bool drivers) const;
	void keepWires(const Net *net);
	void protectPort(const Pin *pin, uint32_t ref);
	RTLIL::Cell *cutPort(const Pin *pin);
	RTLIL::Cell *portBarrier(RTLIL::Module *module, const RTLIL::SigBit &bit) const;
	const Pin *topPortPin(const RTLIL::Cell *barrier, const RTLIL::SigBit &bit) const;
	void protectObject(const void *object, uint32_t ref, const Found &found);
	void protectPin(const Pin *pin, uint32_t ref, const Found &found);
	void protectHierPin(const Pin *pin, uint32_t ref, bool image);
	bool isRegister(const Instance *inst) const;
	bool isClockPin(const Pin *pin) const;
	void protectCell(const Instance *inst, uint32_t ref);
	void protectNet(const Net *net, uint32_t ref);
	void leafDrivers(const Net *net, pool<const Net *> &seen, std::vector<const Pin *> &drivers) const;
	// Anchors: write
	void addAnchor(RTLIL::AttrObject *object, const detail::Anchor &anchor);
	bool markIfShared(RTLIL::AttrObject *object, RTLIL::Module *module);
	void anchorCell(const Instance *inst, detail::Anchor anchor);
	void anchorWires(const Net *net, uint32_t ref);
	void anchorRef(const void *object, uint32_t ref, Found &found, bool barriers);
	void anchorImagePin(const Pin *pin, uint32_t ref, Found &found, bool barriers);
	void anchorDrivers(const Pin *pin, uint32_t ref, Found &found);
	// Anchors: resolve
	const std::vector<detail::Anchor> &anchorsOf(const RTLIL::AttrObject *object) const;
	void addNetHits(const Net *net, const RTLIL::SigBit &bit);
	void indexBarrier(RTLIL::Cell *cell, const Instance *scope);
	void cutPins(const RTLIL::Cell *barrier, const Instance *scope, detail::Anchor::Side side, std::vector<const void *> &found);
	void addCutUser(const ModWalker::PortBit &at, const Instance *scope, bool drivers, std::vector<const void *> &found) const;
	std::vector<const void *> barrierCutPins(const std::vector<detail::Hit> &hits);
	void barrierPins(const std::vector<detail::Hit> &hits, Found &ref);
	std::vector<const void *> resolvePin(const std::vector<detail::Hit> &hits, Found &ref);
	std::vector<const void *> resolveCell(const std::vector<detail::Hit> &hits);
	std::vector<const void *> resolvePort(const std::vector<detail::Hit> &hits, const void *top_pin);
	void topPorts(const Net *net, std::vector<const void *> &pins) const;
	std::vector<const void *> pinsUnder(const Net *net, const std::string &scope) const;
	std::vector<const void *> resolveNet(const std::vector<detail::Hit> &hits, Found &ref);
	std::string cellScope(const Instance *inst) const;
private:
	RTLIL::Design *design_ = nullptr;
	LeafModel *model_ = nullptr;
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
	pool<std::string> unmodeled_; // leaf types that the model does not know

	// Scope contents
	std::unordered_map<const Instance *, ScopeData> scopes_;

	// RTLIL to records
	ListMap<uint32_t, Instance *> cell_insts_;                 // by cell hashidx_
	ListMap<const RTLIL::Module *, Instance *> module_scopes_;
	IdMap<InstData> inst_data_;

	// Nets by bit
	std::map<RTLIL::Module *, SigMap> sigmaps_;
	NetsByScopeBit bit_nets_;
	IdMap<NetData> net_data_;

	// Staleness
	uint64_t fingerprint_ = 0;
	std::vector<std::string> tracked_; // modules with a scope
	mutable bool dirty_ = false;
	mutable bool changed_ = false;

	// Anchors, retire gives the tables to the next view
	std::vector<std::vector<detail::Anchor>> anchor_table_; // by netview_ref value
	dict<int, std::vector<detail::Anchor>> barrier_table_;  // by anchor id
	dict<int, int> barrier_marks_;                          // by anchor id
	int barrier_count_ = 0;                                 // the last anchor id
	IdMap<std::vector<detail::Hit>> hits_;                  // by ref
	dict<RTLIL::SigBit, RTLIL::Cell *> cuts_;
	std::map<RTLIL::Module *, ModWalker> walkers_;
	bool new_images_ = false; // protect made an image, the view changed
};

YOSYS_NAMESPACE_END

#endif
