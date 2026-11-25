#ifndef NETTRACK_INTERNAL_H
#define NETTRACK_INTERNAL_H

#include "kernel/modtools.h"
#include "kernel/netview/nettrack.h"
#include "kernel/netview/netview_internal.h"

#include <optional>

YOSYS_NAMESPACE_BEGIN

namespace detail
{

constexpr std::string_view ref_attr = "\\netview_ref";        // id of a cell, wire or $barrier
constexpr std::string_view cut_on_a_attr = "\\netview_cut_a"; // $barrier at a driver, cut wire on A
constexpr char new_scope_mark = '\t';                         // marks a new scope named as a live scope
constexpr int noted_twins = 2;                                // moved cells that noteHits notes per id and names

using Netlist::InstanceList;
using Netlist::NetList;
using Netlist::PinList;
using PortBit = ModWalker::PortBit;
using ScopeNameSet = pool<std::string>;
using CellSet = pool<const RTLIL::Cell *>;
using CellInScope = std::pair<const Netlist::Instance *, const RTLIL::Cell *>;
using CellBitInScope = std::tuple<const Netlist::Instance *, const RTLIL::Cell *, int>;
using BitInScope = std::pair<const Netlist::Instance *, RTLIL::SigBit>;
using ScopePortBit = std::tuple<const Netlist::Instance *, RTLIL::IdString, int>;
using CellPort = std::pair<RTLIL::Cell *, RTLIL::IdString>;
using WireBitName = std::pair<std::string, int>; // wire name and offset
using NetsByName = std::map<Netlist::NetName, const Netlist::Net *>;

template <typename K, typename V> struct ListMap {
	void add(const K &key, V value) { data[key].push_back(value); }
	const std::vector<V> &get(const K &key) const { return data.at(key, none); }
	dict<K, std::vector<V>> data;
	std::vector<V> none;
};

// where an object was at checkpoint, found by its id
struct Anchor {
	enum class Role : uint8_t {
		Pin,     // leaf or scope pin, no barrier
		CutPin,  // leaf pin with barrier, for when the barrier is gone
		StandIn, // leaf pin below a hierarchical pin or net, for a dissolved scope
		Cell,    // cell of an instance ref
		Barrier, // barrier at a ref pin or at a pin of a ref cell
		Port,    // wire of a top port
		Net,     // wire that names a net
		Scope    // each scope cell of the view, of no ref
	};

	Role role;
	uint32_t ref_index;        // same in checkpoint and resolve
	std::string scope = {};    // scopeNames of the cell or barrier, none for a wire
	std::string own_name = {}; // Scope only, name and a space, scope plus own_name is its scopeNames
	std::string port = {};
	int bit = 0;
	int hdl_index = 0; // declared index of the pin bit
	int net_place = 0; // Net only, index of its NetPlace
	bool hier = false; // Barrier of a hierarchical pin
};
using AnchorList = std::vector<Anchor>;

// where a net of a net ref was at checkpoint
struct NetPlace {
	std::string scope;     // its scopeNames
	std::string dissolved; // scope names in the hdlname of its wire, flatten puts them there
	bool on_port = false;  // flatten joins it with the net above, that is not the old net
	Netlist::NetName name;
};

// what the last checkpoint knows, see NetTracker::checkpoint
struct TrackData {
	static inline int last_id = 0; // process wide, keySeed keeps ids of another yosys run apart

	ListMap<int, Anchor> anchors_by_id; // each list sorted by scope, see noteScopes

	enum class Scope : uint8_t {
		Live,     // view scope
		Dissolved // dissolved by flatten
	};

	dict<std::string, Scope> scopes;            // by scopeNames
	ListMap<uint32_t, Anchor> top_ports_by_ref; // a top pin is also found by port name
	ListMap<uint32_t, NetPlace> net_places_by_ref;
	ListMap<uint32_t, WireBitName> open_bits_by_ref; // at each inout pin of a cell ref, no barrier there
	void noteDissolved(std::string names);
	int nextId(RTLIL::Design *design);
	const AnchorList &anchorsOf(RTLIL::Design *design, const RTLIL::AttrObject *object) const;
};

// puts a $barrier at each pin of a ref, it cuts the pin off its net with a cut wire
struct CheckpointWriter {
	CheckpointWriter(const NetView &view, TrackData &data);
	// makeScopeNamesUnique -> write each ref -> setCutPorts -> noteScopes -> dropUnusedIds
	void write(uint32_t ref_index, const TrackedRef &ref);
	void setCutPorts();
	void noteScopes();
	void dropUnusedIds();
private:
	void addAnchor(RTLIL::AttrObject *object, const Anchor &anchor);
	void anchorPin(const Netlist::Pin *pin, uint32_t ref_index);
	void anchorInnerPins(const Netlist::Net *net, RTLIL::PortDir dir, uint32_t ref_index);
	void anchorNet(const Netlist::Net *net, uint32_t ref_index);
	void anchorIn(const Netlist::Instance *inst, RTLIL::Cell *cell, Anchor anchor);
	void countCutUsers(RTLIL::Module *module);
	void protectDriver(const Netlist::Pin *pin, uint32_t ref_index);
	bool cutPin(const Netlist::Pin *pin, uint32_t ref_index);
	void keepCell(const Netlist::Instance *inst);
	void protectCell(const Netlist::Instance *inst, uint32_t ref_index);
	void protectNet(const Netlist::Net *net, uint32_t ref_index);
	RTLIL::Cell *ensureBarrierAtPin(const Netlist::Pin *pin, uint32_t ref_index);
	RTLIL::Cell *createBarrierCell(RTLIL::Module *module, RTLIL::SigBit bit, bool cut_on_a);
	const NetView &view_;
	TrackData &data_;
	dict<RTLIL::SigBit, RTLIL::Cell *> barrier_by_cut_bit_;
	dict<CellPort, RTLIL::SigSpec> cut_ports_; // new signal of each port with a cut bit
	dict<RTLIL::SigBit, int> cut_users_;       // cell pins on each cut bit
	std::vector<RTLIL::Cell *> tracked_cells_; // had an id before the checkpoint
	pool<const RTLIL::AttrObject *> anchored_;
	dict<const RTLIL::Module *, ScopeNameSet> gone_scopes_by_module_; // from the hdlname of each anchored cell
};

enum class WalkTarget : uint8_t { Drivers, Loads }; // pins a walk along a cut wire looks for

enum class WalkReach : uint8_t {
	CutSide, // stops at a barrier with anchors, fails on a load outside the scope or a driver outside the top
	AllLoads // passes both, a top output is a load
};

struct CutWalk {
	WalkReach reach = WalkReach::CutSide;
	bool stop_at_scope = false;  // a scope on the wire gives its pin, no walk below
	pool<CellBitInScope> passed; // barriers and buffers, per bit
	pool<BitInScope> seen;
	pool<ScopePortBit> exit_ports; // walk went up through them
	PinList pins;
};

struct AnchorHit {
	const Anchor *anchor;
	const Netlist::Instance *scope; // holds the cell
	const RTLIL::Cell *cell;        // of the instance, or the barrier
	std::string now = {};           // candidate only, scope names of the cell in the view
};
using HitList = std::vector<AnchorHit>;
using HitPtrList = std::vector<const AnchorHit *>;

enum class AnchorKind : uint8_t {
	Scopes, // take candidates first, they tell which scopes are gone
	Objects
};

// finds the anchors in the view in build order, turns the hits of each ref into objects
struct Resolver {
	Resolver(const NetView &view, const TrackData &data);
	void resolve(uint32_t ref_index, TrackedRef &ref);
private:
	using MovedCell = std::pair<const AnchorList *, std::string>; // anchors of its id and its names now
	using PortPlace = std::tuple<uint32_t, std::string, int>;     // ref, port name and bit of the checkpoint

	void enterScope(const Netlist::Instance *scope, const std::string &names);
	void noteHits(const Netlist::Instance *scope, const RTLIL::Cell *cell);
	void addHit(const AnchorHit &hit);
	bool enterNamedScopes();
	size_t goneScopeEnd(std::string_view old, size_t at) const;
	bool namesAlign(std::string_view old, std::string_view now) const;
	bool takeCandidates(AnchorKind kind);
	void markCandidateScopesLive();
	HitPtrList alignedCandidates(const HitList &hits) const;
	const AnchorHit *onlyCandidate(const HitList &candidates) const;
	void noteWires(const Netlist::Instance *scope);
	void noteNamedNet(const Netlist::Instance *scope, const RTLIL::Wire *wire, const Anchor &anchor);
	const NetsByName &netsByName(const Netlist::Instance *scope);

	void resolveInstance(uint32_t ref_index, TrackedRef &ref);
	PinList resolvePin(uint32_t ref_index);
	PinList hitPins(uint32_t ref_index, Anchor::Role role);
	PinList cutPins(const AnchorHit &hit, WalkReach reach = WalkReach::CutSide);
	const ModWalker &walkerOf(RTLIL::Module *module);
	// walk along a cut wire, false when the ref is lost
	bool addCutPins(const Netlist::Instance *scope, RTLIL::SigBit bit, WalkTarget target, CutWalk &walk);
	bool passPorts(const Netlist::Instance *scope, RTLIL::SigBit root, WalkTarget target, CutWalk &walk);
	bool addUserPins(const Netlist::Instance *scope, const PortBit &at, WalkTarget target, CutWalk &walk);
	bool passBarrier(const Netlist::Instance *scope, const PortBit &at, WalkTarget target, CutWalk &walk);
	bool addLeafPin(const Netlist::Pin *pin, const PortBit &at, WalkTarget target, CutWalk &walk);
	bool passCell(const Netlist::Instance *scope, const PortBit &at, WalkTarget target, CutWalk &walk);
	bool addPinsAbove(const Netlist::Instance *scope, RTLIL::SigBit root, WalkTarget target, CutWalk &walk);
	bool addPinsBelow(const Netlist::Instance *inst, const PortBit &at, WalkTarget target, CutWalk &walk);
	InstanceList cellsBetween(uint32_t ref_index, bool has_id);
	bool isWiredOutput(const AnchorHit &hit, const PinList &cut_side);
	bool isFedOnlyBy(InstanceList todo, const InstanceList &cells, const InstanceList &between);
	bool queueDriversBetween(const Netlist::Pin *input, const InstanceList &cells, const InstanceList &between, pool<const Netlist::Instance *> &seen, InstanceList &todo);
	const InstanceList &driverCells(const Netlist::Net *net);
	InstanceList cellsUpTo(const HitList &hits, const pool<RTLIL::SigBit> &ends, bool has_id);
	CellSet cellsToward(const HitList &hits, const pool<RTLIL::SigBit> &ends, WalkTarget target);
	PinList loadsBehind(const AnchorHit &hit);
	NetList resolveNet(uint32_t ref_index);
	void addNetsAt(const NetPlace &place, const PinList &drivers, NetList &nets) const;
	const Netlist::Net *netInScope(const Netlist::Net *net, const NetPlace &old) const;
	const NetView &view_;
	const TrackData &data_;
	ListMap<std::pair<uint32_t, Anchor::Role>, AnchorHit> hits_by_ref_role_;
	ListMap<const Anchor *, AnchorHit> candidates_;
	pool<const Anchor *> anchors_with_hit_;
	dict<MovedCell, int> moved_cell_count_;                   // cells not at an old place
	dict<CellInScope, const Anchor *> place_by_cell_;         // anchor of its first hit, a cell was at one place
	InstanceList named_scopes_;                               // wait for enterNamedScopes
	ScopeNameSet live_scopes_;                                // entered scopes and scopes with a candidate
	dict<PortPlace, const Netlist::Pin *> port_pin_by_place_; // top pin at the anchored port wire
	ListMap<const NetPlace *, const Netlist::Net *> named_nets_by_place_;
	std::map<uint32_t, NetsByName> nets_by_scope_name_; // by scope id, see netsByName
	std::map<RTLIL::Module *, ModWalker> mod_walkers_;
	// by instance id, checkpoint scopeNames or names of now for a new scope, none when not entered (twins and below)
	std::vector<std::optional<std::string>> scope_names_;
	dict<const Netlist::Net *, InstanceList> driver_cells_by_net_; // see driverCells
};

void makeScopeNamesUnique(const NetView &view);
std::string scopeNames(const Netlist::Instance *scope, std::string names = {});
std::optional<int> refIdOf(RTLIL::Design *design, const RTLIL::AttrObject *object);
int keySeed(RTLIL::Design *design);
Anchor pinAnchor(const Netlist::Pin *pin, uint32_t ref_index, Anchor::Role role = Anchor::Role::Pin);
bool isAtOrBelow(const Netlist::Instance *inst, const Netlist::Instance *scope);
// leaf pins on a net and its connected nets, in a scope and below
struct LeafPinsOnNet {
	PinList inside; // of the wanted direction
	bool has_load_inside = false;
};
void addLeafPins(const Netlist::Net *net, RTLIL::PortDir dir, LeafPinsOnNet &found);
PinList standInPins(const Netlist::Net *net, RTLIL::PortDir dir);
void ensureHdlname(RTLIL::Cell *cell);
bool isLeafDriver(const Netlist::Pin *pin);
bool isTieCell(const Netlist::Instance *inst);
InstanceList newDrivers(const TrackedRef &ref);
bool isBetween(const Netlist::Instance *inst, const InstanceList &between);
bool isAllBetween(const InstanceList &cells, const InstanceList &between);

void setOwnedAttribute(RTLIL::Design *design, RTLIL::AttrObject *object, RTLIL::IdString attr);
void removeOwnedKeeps(RTLIL::Design *design);
bool cutOnA(const RTLIL::Cell *barrier);
RTLIL::SigBit cutBit(const RTLIL::Cell *barrier);
std::vector<RTLIL::Cell *> trackedCells(RTLIL::Design *design);
const Netlist::Pin *findPortPin(const Netlist::Instance *inst, const Anchor &anchor);

template <typename T> std::vector<const T *> uniqueSorted(std::vector<const T *> objects)
{
	std::ranges::sort(objects, {}, &T::id);
	objects.erase(std::unique(objects.begin(), objects.end()), objects.end());
	return objects;
}

} // namespace detail

YOSYS_NAMESPACE_END

#endif
