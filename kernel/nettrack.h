// Tracking: refs find their objects again after passes:
// - epoch end  EpochSnapshot takes the names, AnchorWriter writes anchors, BarrierWriter puts barriers (EpochEndData, retire moves it)
// - rebuild    ViewBuilder builds the view, HitIndex notes where the anchors landed in it
// - resolve    Resolver turns the hits into objects, CutSideWalker walks from a barrier to the pins on its cut side
// Rules:
// - a ref resolves to its own cut side only (CutSideWalker)
// - identity is the signal plus the name at the epoch end (ScopePaths)
// - a removed hierarchical pin is the leaf set that OpenSTA takes for it

#ifndef NETTRACK_H
#define NETTRACK_H

#include "kernel/modtools.h"
#include "kernel/netlist.h"
#include "kernel/rtlil.h"

#include <deque>
#include <map>
#include <optional>
#include <string_view>

YOSYS_NAMESPACE_BEGIN

struct NetView;

enum class Protection : uint8_t {
	AnchorsOnly,
	Barriers
};

enum class WalkTarget : uint8_t {
	Drivers,
	Loads
};

struct PortRename {
	std::string old_port;
	std::string new_port;
	const void *cell; // of the new port
};

struct TrackedRef {
	enum class ObjectKind : uint8_t {
		Pin,
		Cell,
		Net,
		Port // of the top, as its pin
	};

	// Req of the consumer
	struct Request {
		bool isolate_cell = false;          // of a leaf pin, keep each path through its cell
		bool wants_image = false;           // protect makes its barrier an image
		const void *top_port_pin = nullptr; // of a port by name, set before resolve
	};

	// Facts that the epoch end finds
	struct AnchorFacts {
		Netlist::Dir hier_dir = Netlist::Dir::Unknown; // of a hierarchical pin, Input or Output
		bool is_image_pin = false;
		bool moved_to_drivers = false; // an image A pin anchored on its drivers
		bool isHierarchicalPin() const;
	};

	struct Result {
		std::vector<const void *> exact_pins = {};   // the leaf pin itself, objects holds the pins on its cut side
		std::vector<const void *> loads_beyond = {}; // beyond its barrier, or beyond the outputs of a cell
		std::vector<const void *> image_a_pins = {};
		std::vector<const void *> image_y_pins = {};
		std::vector<const void *> through_pins = {}; // of a net in its old scope
		std::vector<PortRename> port_renames = {};
		bool found_as_leaf_pins = false; // a hierarchical pin found as its leaf pins inside
	};

	ObjectKind kind;
	Request request = {};
	AnchorFacts facts = {};
	std::vector<const void *> objects = {}; // set before the epoch end, resolve finds them again
	Result result = {};
};

namespace detail {

// Attribute and name strings
constexpr std::string_view anchor_prefix = "netview_anchor";
constexpr std::string_view anchor_attr = "\\netview_anchor";
constexpr std::string_view ref_attr = "\\netview_ref";
constexpr std::string_view cut_attr = "\\netview_cut";
constexpr std::string_view owned_marker_prefix = "\\netview_";

enum class IdLookup : uint8_t {
	FindOnly,
	AddIfMissing
};

enum class CutWireSide : uint8_t {
	OnCutWire,
	OffCutWire
};

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
	uint32_t ref_index;
	std::string scope_path; // with the own scope of the cell or wire
	std::string port;
	int bit;
	std::string net_scope_path; // of the scope that holds the wire
	bool in_shared_module;
	Side side = Side::None;
};

enum class BarrierMark : uint8_t {
	CutOnA,  // the cut wire is on A, at an output
	PortCut, // the cut side holds all uses of a port bit
	Image    // an instance in the view, keeps a hierarchical pin
};

struct BarrierMarks {
	uint8_t bits = 0;
	bool has(BarrierMark mark) const;
	void add(BarrierMark mark);
};

// An anchor that the rebuilt view holds
struct AnchorHit {
	Anchor anchor;
	const Netlist::Instance *instance; // of a cell anchor
	const Netlist::Net *net;           // of a wire anchor
	bool in_own_scope;
	const RTLIL::Cell *barrier = nullptr; // of a barrier anchor
	const Netlist::Instance *barrier_scope = nullptr;
};

struct CutSideWalkState {
	const Netlist::Instance *scope;
	WalkTarget target;
	std::vector<const void *> &reached_pins;
};

struct EpochSnapshot {
	dict<uint32_t, std::string> cell_names;
	void take(const NetView &view, const std::deque<Netlist::Instance> &instances);
	void clear();
};

struct AnchorStore {
	std::vector<std::vector<Anchor>> anchors_by_ref_attr;
	void append(RTLIL::Design *design, RTLIL::AttrObject *object, const Anchor &anchor);
	const std::vector<Anchor> &anchorsOf(RTLIL::Design *design, const RTLIL::AttrObject *object) const;
	void clear();
};

struct BarrierStore {
	ListMap<int, Anchor> anchors_by_barrier;
	dict<int, BarrierMarks> marks_by_barrier;
	int last_barrier_id = 0;
	int nextId();
	void addMark(const RTLIL::Cell *barrier, BarrierMark mark);
	bool hasMark(const RTLIL::Cell *barrier, BarrierMark mark) const;
	RTLIL::IdString cutPort(const RTLIL::Cell *barrier) const;
	void clearMarks();
	void clearAnchors();
};

// Stuff the epoch end wrote
struct EpochEndData {
	EpochSnapshot snapshot;
	AnchorStore anchors;
	BarrierStore barriers;
};

struct HitIndex {
	IdMap<std::vector<AnchorHit>> hits_by_ref;
	dict<RTLIL::SigBit, RTLIL::Cell *> barrier_by_cut_bit;
	void noteInstance(const NetView &view, const EpochEndData &epoch, const Netlist::Instance *inst);
	void noteWireBit(const NetView &view, const EpochEndData &epoch, const Netlist::Net *net, const RTLIL::SigBit &bit);
	void noteBarrier(const NetView &view, const EpochEndData &epoch, RTLIL::Cell *cell, const Netlist::Instance *scope);
	const std::vector<AnchorHit> &hitsOf(uint32_t ref_index) const;
	void clear();
};

// Path identity
struct ScopePaths {
	const NetView &view;
	const EpochSnapshot &snapshot;
	std::string scopePath(const Netlist::Instance *scope) const;
	std::string cellScopePath(const Netlist::Instance *inst) const;
};

// The leaf pins on the cut side of a barrier, across chains of barriers
class CutSideWalker {
public:
	CutSideWalker(const NetView &view, const BarrierStore &barriers);
	void pins(const RTLIL::Cell *barrier, const Netlist::Instance *scope, Anchor::Side side, std::vector<const void *> &out);
	void clear();
private:
	void walkBarrier(CutSideWalkState &walk, const RTLIL::Cell *barrier);
	void walkSignal(CutSideWalkState &walk, const RTLIL::Cell *from, const RTLIL::SigBit &bit, CutWireSide cut_side);
	bool entersBarrier(const CutSideWalkState &walk, const ModWalker::PortBit &at, CutWireSide cut_side) const;
	void walkUser(CutSideWalkState &walk, const ModWalker::PortBit &at);
	const Netlist::Pin *topPortPinOf(const RTLIL::SigBit &bit, const ModWalker &walker);

	const NetView &view_;
	const BarrierStore &barriers_;
	std::map<RTLIL::Module *, ModWalker> mod_walkers_;
	dict<RTLIL::SigBit, const Netlist::Pin *> top_port_pin_by_bit_; // by top SigMap bit
};

// The anchors of the objects of a ref at the epoch end
class AnchorWriter {
public:
	AnchorWriter(const NetView &view, EpochEndData &epoch, CutSideWalker &walker);
	void write(const void *object, uint32_t ref_index, TrackedRef &ref, Protection protection);
private:
	void anchorPin(const Netlist::Pin *pin, uint32_t ref_index, TrackedRef &ref, Protection protection);
	void anchorImagePin(const Netlist::Pin *pin, uint32_t ref_index, TrackedRef &ref, Protection protection);
	void anchorDriversOfImage(const Netlist::Pin *pin, uint32_t ref_index, TrackedRef &ref);
	void anchorCell(const Netlist::Instance *inst, Anchor anchor);
	void anchorWires(const Netlist::Net *net, uint32_t ref_index);
	bool markIfShared(RTLIL::AttrObject *object, RTLIL::Module *module);

	const NetView &view_;
	EpochEndData &epoch_;
	CutSideWalker &walker_;
	ScopePaths paths_;
};

class BarrierWriter {
public:
	BarrierWriter(const NetView &view, EpochEndData &epoch, HitIndex &hit_index);
	void protect(const void *object, uint32_t ref_index, const TrackedRef &ref);
	bool madeNewImage() const;
private:
	void protectPin(const Netlist::Pin *pin, uint32_t ref_index, const TrackedRef &ref);
	void protectLeafPin(const Netlist::Pin *pin, uint32_t ref_index, const std::string &net_scope_path = "");
	void protectHierPin(const Netlist::Pin *pin, uint32_t ref_index, bool wants_image);
	void protectPort(const Netlist::Pin *pin, uint32_t ref_index);
	void protectCell(const Netlist::Instance *inst, uint32_t ref_index);
	void protectNet(const Netlist::Net *net, uint32_t ref_index);
	void isolateCell(const Netlist::Instance *inst);
	void anchorPinBarrier(const Netlist::Pin *pin, uint32_t ref_index, const std::string &net_scope_path = "");
	RTLIL::Cell *ensureBarrierAtPin(const Netlist::Pin *pin);
	RTLIL::Cell *ensureBarrierAtPort(const Netlist::Pin *pin);
	RTLIL::Cell *findPortBarrier(RTLIL::Module *module, const RTLIL::SigBit &bit) const;
	RTLIL::Cell *createBarrierCell(RTLIL::Module *module, const RTLIL::SigBit &a, const RTLIL::SigBit &y);
	void markWiresKeep(const Netlist::Net *net);
	void collectLeafDrivers(const Netlist::Net *net, pool<const Netlist::Net *> &seen, std::vector<const Netlist::Pin *> &drivers) const;
private:
	const NetView &view_;
	EpochEndData &epoch_;
	HitIndex &hit_index_;
	ScopePaths paths_;
	bool made_new_image_ = false; // the view changed
};

// The objects of a ref from its hits in the rebuilt view
class Resolver {
public:
	Resolver(const NetView &view, const EpochEndData &epoch, const HitIndex &hit_index, CutSideWalker &walker);
	void resolve(uint32_t ref_index, TrackedRef &ref);
private:
	std::vector<const void *> resolveObjects(const std::vector<AnchorHit> &hits, TrackedRef &ref);
	std::vector<const void *> cutSidePinsOfHits(const std::vector<AnchorHit> &hits);
	void collectLoadsBeyondAndImagePins(const std::vector<AnchorHit> &hits, TrackedRef &ref);
	std::vector<const void *> resolvePin(const std::vector<AnchorHit> &hits, TrackedRef &ref);
	std::vector<const void *> pinsBehindNewLogic(const std::vector<const Netlist::Instance *> &insts, const std::vector<const void *> &cut) const;
	void addOutputLoads(const Netlist::Instance *inst, std::vector<const void *> &loads) const;
	std::vector<const void *> resolveCell(const std::vector<AnchorHit> &hits);
	std::vector<const void *> resolvePort(const std::vector<AnchorHit> &hits, const void *top_port_pin);
	void collectTopPorts(const Netlist::Net *net, std::vector<const void *> &pins) const;
	std::vector<const void *> leafPinsUnderScope(const Netlist::Net *net, const std::string &scope_path) const;
	const Netlist::Net *netInScope(const Netlist::Net *net, const std::string &scope_path) const;
	std::vector<const void *> resolveNet(const std::vector<AnchorHit> &hits, TrackedRef &ref);
	std::vector<PortRename> portRenames(const std::vector<AnchorHit> &hits, const std::vector<const void *> &cells);
private:
	const NetView &view_;
	const HitIndex &hit_index_;
	CutSideWalker &walker_;
	ScopePaths paths_;
};

// Ids
RTLIL::IdString attrId(RTLIL::Design *design, std::string_view name, IdLookup lookup);
RTLIL::IdString refAttrId(RTLIL::Design *design, IdLookup lookup);
RTLIL::IdString ownedMarkerId(RTLIL::Design *design, RTLIL::IdString attr, IdLookup lookup);

// Attributes
void ensureScopename(RTLIL::AttrObject *object);
void setOwnedAttribute(RTLIL::Design *design, RTLIL::AttrObject *object, RTLIL::IdString attr);
void removeOwnedMarks(RTLIL::Design *design, RTLIL::AttrObject *object);

// Barriers
RTLIL::Wire *addCutWire(RTLIL::Module *module);
bool isCutWire(const RTLIL::Wire *wire);
std::optional<int> barrierIdOf(const RTLIL::Cell *barrier);
void recordBarrierAnchor(const NetView &view, BarrierStore &barriers, RTLIL::Cell *barrier, const std::string &path, Anchor anchor);
void replaceBitInModule(RTLIL::Module *module, const RTLIL::SigBit &bit, const RTLIL::SigBit &other);

// Walks
Netlist::Dir pinDirOfTarget(WalkTarget target);
RTLIL::IdString barrierPortToward(WalkTarget target);
bool pinMatchesTarget(const Netlist &netlist, const Netlist::Pin *pin, WalkTarget target);

// Scope paths
bool hasOwnScope(const RTLIL::AttrObject *object);
std::vector<std::string> ownScopeParts(const RTLIL::AttrObject *object);
std::string joinScopePath(const std::vector<std::string> &parts);
std::string ownInstanceName(const Netlist::Instance *scope);
std::string withOwnScope(const std::string &path, const RTLIL::AttrObject *object);
std::string barrierScopePath(const std::string &path, const RTLIL::Cell *barrier);

// Resolve
std::vector<const AnchorHit *> hitsOfRole(const std::vector<AnchorHit> &hits, Anchor::Role role);
std::vector<const void *> uniqueSorted(std::vector<const void *> objects);
std::vector<const void *> hierPinsAbove(const std::vector<const Netlist::Instance *> &insts, const std::vector<const void *> &leaves);

} // namespace detail

YOSYS_NAMESPACE_END

#endif
