#ifndef NETTRACK_INTERNAL_H
#define NETTRACK_INTERNAL_H

#include "kernel/modtools.h"
#include "kernel/nettrack.h"
#include "kernel/netview_internal.h"

#include <optional>

YOSYS_NAMESPACE_BEGIN

namespace detail
{

constexpr std::string_view ref_attr = "\\netview_ref";        // the id of a cell, wire or $barrier
constexpr std::string_view cut_on_a_attr = "\\netview_cut_a"; // a $barrier at a driver, its cut wire is on A
constexpr char new_scope_mark = '\t';                        // on a new scope with the name of a live scope
constexpr int noted_twins = 2;                               // noteHits notes so many moved cells of one id and names

using PinList = std::vector<const Netlist::Pin *>;
using InstanceList = std::vector<const Netlist::Instance *>;
using NetList = std::vector<const Netlist::Net *>;
using PortBit = ModWalker::PortBit; // a bit of a cell port on a signal

template <typename K, typename V> struct ListMap {
	void add(const K &key, V value) { data[key].push_back(value); }
	const std::vector<V> &get(const K &key) const { return data.at(key, none); }
	dict<K, std::vector<V>> data;
	std::vector<V> none;
};

// where an object was at checkpoint, found by its id
struct Anchor {
	// a Pin is a leaf or scope pin with no barrier, a CutPin a leaf pin with one, for when the barrier is gone
	// a StandIn is a leaf pin below a hierarchical pin or net, it stands in when flatten dissolved the scope
	// a Net is on the wire that names a net, a Scope is on the cell of each scope of the view, of no ref
	enum class Role : uint8_t { Pin, CutPin, StandIn, Cell, Barrier, Port, Net, Scope };

	Role role;
	uint32_t ref_index;              // index into this checkpoint's refs, same in checkpoint and resolve
	std::string scope = {};          // of the cell or barrier, see scopeNames, a wire has none
	std::string own_name = {};       // of a Scope with a space after, scope and own_name are its scopeNames
	std::string port = {};           // of a pin
	int bit = 0;
	int hdl_index = 0;               // of a pin, the declared index of the bit
	int net_place = 0;               // of a Net, the position of its NetPlace
	bool hier = false;               // Barrier of a hierarchical pin
};
using AnchorList = std::vector<Anchor>;

// scopeNames of the scope and the name of each net of a net ref
struct NetPlace {
	std::string scope;
	std::string dissolved; // the scope names in the hdlname of its wire, flatten puts them there
	bool on_port = false; // flatten of its scope joins it with the net above, that net is not the old net
	Netlist::NetName name;
};

struct TrackData {
	static inline int last_id = 0; // process wide, seeded by keySeed so the ids of another yosys run do not match

	// from the last checkpoint
	ListMap<int, Anchor> anchors_by_id; // each list in the order of the scope names
	// Live is a scope of the view, Dissolved one that flatten dissolved, the hdlname of an anchored cell names it
	enum class Scope : uint8_t { Live, Dissolved };
	dict<std::string, Scope> scopes; // by scopeNames
	ListMap<uint32_t, Anchor> top_ports_by_ref; // port, bit and hdl_index of each top pin, found by name
	ListMap<uint32_t, NetPlace> net_places_by_ref;
	// wire and offset at each inout pin of a cell ref, it has no barrier
	ListMap<uint32_t, std::pair<std::string, int>> open_bits_by_ref;
	int nextId(RTLIL::Design *design);
	void noteDissolved(std::string names);
	const AnchorList &anchorsOf(RTLIL::Design *design, const RTLIL::AttrObject *object) const;
};

// puts a $barrier at each pin of a ref, it cuts the pin off its net with a cut wire
struct CheckpointWriter {
	CheckpointWriter(const NetView &view, TrackData &data, bool protect);
	void write(uint32_t ref_index, const TrackedRef &ref);
	// after the last write and makeScopeNamesUnique, anchors the cell of each scope, sorts each anchor list by scope
	void noteScopes();
	// after the last anchor, a cell with no anchor loses its id, a barrier gets a new one
	void dropUnusedIds();
private:
	void countCutUsers(RTLIL::Module *module);
	void append(RTLIL::AttrObject *object, const Anchor &anchor); // gives the cell or wire an id when it has none
	void anchorPin(const Netlist::Pin *pin, uint32_t ref_index);
	// on a cell or barrier in the parent scope of the instance
	void anchorIn(const Netlist::Instance *inst, RTLIL::Cell *cell, Anchor anchor);
	void anchorInnerPins(const Netlist::Net *net, RTLIL::PortDir dir, uint32_t ref_index);
	void protectDriver(const Netlist::Pin *pin, uint32_t ref_index);
	void keepCell(const Netlist::Instance *inst); // keep on a leaf cell, keep_hierarchy on a scope cell
	void protectCell(const Netlist::Instance *inst, uint32_t ref_index); // keepCell and a barrier at each leaf pin
	void protectNet(const Netlist::Net *net, uint32_t ref_index);
	// the only place that makes a Barrier anchor, false if the pin gets no barrier
	bool cutPin(const Netlist::Pin *pin, uint32_t ref_index);
	// notes the wire bit at an inout pin, it gets no barrier
	RTLIL::Cell *ensureBarrierAtPin(const Netlist::Pin *pin, uint32_t ref_index);
	RTLIL::Cell *createBarrierCell(RTLIL::Module *module, RTLIL::SigBit bit, bool cut_on_a); // with a new cut wire
	const NetView &view_;
	TrackData &data_;
	bool protect_;
	dict<RTLIL::SigBit, RTLIL::Cell *> barrier_by_cut_bit_;
	dict<RTLIL::SigBit, int> cut_users_; // by cut bit, the cell pins on it
	std::vector<RTLIL::Cell *> tracked_cells_; // had an id before the checkpoint
	pool<const RTLIL::AttrObject *> anchored_; // the cells and wires with an anchor
	// by the module of each anchored cell, the scope names in its hdlname
	dict<const RTLIL::Module *, pool<std::string>> gone_scopes_by_module_;
};

enum class WalkTarget : uint8_t { Drivers, Loads }; // the pins that a walk along a cut wire looks for

enum class WalkReach : uint8_t {
	CutSide, // stops at a barrier with anchors, fails when the target is outside the scope
	AllLoads // passes both, a top output is a load
};

// what a walk along a cut wire went through
struct CutWalk {
	WalkReach reach = WalkReach::CutSide;
	bool stop_at_scope = false; // a scope on the wire gives its pin, the walk does not go below
	pool<std::pair<const Netlist::Instance *, const RTLIL::Cell *>> passed; // barriers and buffers
	pool<std::pair<const Netlist::Instance *, RTLIL::SigBit>> seen;      // signals by scope
	PinList pins;
};

struct AnchorHit {
	const Anchor *anchor;
	const Netlist::Instance *scope; // holds the cell
	const RTLIL::Cell *cell;        // of the instance, or the barrier
	std::string now = {};           // of a candidate, the scope names of the cell in the view
};

// which anchors take their candidates, the scopes go first, they tell which scopes are gone
enum class AnchorKind : uint8_t { Scopes, Objects };

// finds the anchors in the view in build order, turns the hits of each ref into objects
struct Resolver {
	Resolver(const NetView &view, const TrackData &data);
	void resolve(uint32_t ref_index, TrackedRef &ref);
private:
	void resolveInstance(uint32_t ref_index, TrackedRef &ref);
	// gives the scope its names, notes the hits of its cells and barriers, enters each new scope below
	// one with a Scope anchor waits for its hit, one with the names of a checkpoint scope for enterNamedScopes
	void enterScope(const Netlist::Instance *scope, const std::string &names);
	// an anchor of the cell with the scope names of this place is a hit, with names that align it is a candidate
	void noteHits(const Netlist::Instance *scope, const RTLIL::Cell *cell);
	void addHit(const AnchorHit &hit);
	// the offset in old after the next scope that the view had at the checkpoint and has no more, else npos
	// the names of scopes that flatten dissolved before the checkpoint go with it, an hdlname has them
	size_t goneScopeEnd(std::string_view old, size_t at) const;
	// true when now can be the place of old, now lacks the names of the scopes that are gone
	// and has one more name for each scope that is new since the checkpoint, submod makes one
	bool namesAlign(std::string_view old, std::string_view now) const;
	// an anchor with no hit takes its one candidate, of two twins it takes none, false when no anchor took one
	bool takeCandidates(AnchorKind kind);
	// a scope with a candidate lives, also when a twin keeps it out
	// a cell with no scope name is then no cell out of it, so they are all marked before an anchor takes one
	void markCandidateScopesLive();
	// those with names that still align and a cell of no other old place
	std::vector<const AnchorHit *> alignedCandidates(const std::vector<AnchorHit> &hits) const;
	// a scope with no anchor and the names of a checkpoint scope is that scope when the view has no other
	// design -load brings cells with no id, submod can reuse the old name of a renamed scope, false when none
	bool enterNamedScopes();
	// the top pin at each anchored port wire by its name now, the net at each anchored net wire
	void noteWires(const Netlist::Instance *scope);
	// the net that each anchored wire at its old place names, or none, a net on a port only in its old scope
	void noteNamedNet(const Netlist::Instance *scope, const RTLIL::Wire *wire, const Anchor &anchor);

	PinList resolvePin(uint32_t ref_index);
	// the pin of each hit of a pin role, a hit with no such port gives none
	PinList hitPins(uint32_t ref_index, Anchor::Role role);
	// the leaf pins on the cut wire of the barrier
	PinList cutPins(const AnchorHit &hit, WalkReach reach = WalkReach::CutSide);
	// the pins on the signal of the bit
	bool addCutPins(const Netlist::Instance *scope, RTLIL::SigBit bit, WalkTarget target, CutWalk &walk);
	// the pins at one user of the signal
	bool addUserPins(const Netlist::Instance *scope, const PortBit &at, WalkTarget target, CutWalk &walk);
	bool passBarrier(const Netlist::Instance *scope, const PortBit &at, WalkTarget target, CutWalk &walk);
	bool addLeafPin(const Netlist::Pin *pin, const PortBit &at, WalkTarget target, CutWalk &walk);
	// walks on from each other one bit port of the cell
	bool passCell(const Netlist::Instance *scope, const PortBit &at, WalkTarget target, CutWalk &walk);
	const ModWalker &walkerOf(RTLIL::Module *module);
	// the loads outside the scope on an output port of its module
	bool addLoadsAbove(const Netlist::Instance *scope, RTLIL::SigBit root, CutWalk &walk);
	// the loads inside a hierarchical instance on its input port, or the drivers on its output port
	bool addPinsBelow(const Netlist::Instance *inst, const PortBit &at, WalkTarget target, CutWalk &walk);
	InstanceList cellsBetween(uint32_t ref_index);
	// the cells from the cut wires up to a barrier or an end bit
	InstanceList cellsUpTo(const std::vector<AnchorHit> &hits, const pool<RTLIL::SigBit> &ends);
	PinList loadsBehind(const AnchorHit &hit);
	NetList resolveNet(uint32_t ref_index);
	const Netlist::Net *netInScope(const Netlist::Net *net, const NetPlace &old) const;
	const NetView &view_;
	const TrackData &data_;
	ListMap<std::pair<uint32_t, Anchor::Role>, AnchorHit> hits_by_ref_role_;
	ListMap<const Anchor *, AnchorHit> candidates_;
	pool<const Anchor *> anchors_with_hit_;
	// by the anchors of its id and its names now, the cells that are not at an old place
	dict<std::pair<const AnchorList *, std::string>, int> moved_cell_count_;
	// by scope instance and cell, the anchor of its first hit, a cell was at one place
	dict<std::pair<const Netlist::Instance *, const RTLIL::Cell *>, const Anchor *> place_by_cell_;
	InstanceList named_scopes_;
	pool<std::string> live_scopes_; // the scopeNames of each entered scope, and of each scope with a candidate
	// by ref, port name and bit of the checkpoint, the top pin at the anchored port wire
	dict<std::tuple<uint32_t, std::string, int>, const Netlist::Pin *> port_pin_by_place_;
	ListMap<const NetPlace *, const Netlist::Net *> named_nets_by_place_;
	// by scope id, the first net of each name, made at the first Net anchor of the scope
	std::map<uint32_t, std::map<Netlist::NetName, const Netlist::Net *>> nets_by_scope_name_;
	std::map<RTLIL::Module *, ModWalker> mod_walkers_;
	// by instance id, the scopeNames of a scope at the checkpoint, a new scope has its names of now
	// none for a scope that is not entered, twins and the scopes below them
	std::vector<std::optional<std::string>> scope_names_;
};

// the names of the scopes of a cell from the top with a space after each, without a cell those of the scope
// flatten keeps the names of the dissolved scopes of a cell in its hdlname
std::string scopeNames(const Netlist::Instance *scope, const RTLIL::AttrObject *object = nullptr);
// an hdlname on each scope cell, see ensureHdlname, then no two scopes of the view have the same scopeNames
// a flatten copy with the names of another scope in its hdlname gets the name of its cell
void makeScopeNamesUnique(const NetView &view);
// an hdlname with the name of the cell, flatten then keeps that name and puts the scope names in front
// a rename makes it stale, so each checkpoint sets it again when it has no scope names
void ensureHdlname(RTLIL::Cell *cell);
Anchor pinAnchor(const Netlist::Pin *pin, uint32_t ref_index, Anchor::Role role = Anchor::Role::Pin);
// the leaf pins on the net in its scope and below, they stand in when flatten dissolves the scope
// PD_INPUT takes the loads, PD_OUTPUT the drivers, PD_INOUT both, an output with a load inside the loads outside
// none when a second port of the scope is on the net
PinList standInPins(const Netlist::Net *net, RTLIL::PortDir dir);
int keySeed(RTLIL::Design *design);
void setOwnedAttribute(RTLIL::Design *design, RTLIL::AttrObject *object, RTLIL::IdString attr);
void removeOwnedKeeps(RTLIL::Design *design);

std::optional<int> refIdOf(RTLIL::Design *design, const RTLIL::AttrObject *object);
bool cutOnA(const RTLIL::Cell *barrier);
RTLIL::SigBit cutBit(const RTLIL::Cell *barrier);
std::vector<RTLIL::Cell *> trackedCells(RTLIL::Design *design); // the cells with an id

// splitnets -ports names a bit port[index]
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
