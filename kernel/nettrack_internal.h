#ifndef NETTRACK_INTERNAL_H
#define NETTRACK_INTERNAL_H

#include "kernel/modtools.h"
#include "kernel/nettrack.h"
#include "kernel/netview_internal.h"

#include <map>
#include <optional>
#include <string_view>

YOSYS_NAMESPACE_BEGIN

namespace detail
{

constexpr std::string_view anchor_prefix = "netview_anchor";
constexpr std::string_view anchor_attr = "\\netview_anchor";
constexpr std::string_view ref_attr = "\\netview_ref";
constexpr std::string_view marks_attr = "\\netview_marks";
constexpr std::string_view tracker_key = "netview.tracker";

// whether a cut side walk toward drivers passes new buffers
// toward loads it always does, insbuf buffer loads are the pin's
// toward the drivers the buffer can be the new driver
enum class BufferRule : uint8_t { StopAtNewBuffer, PassNewBuffer };

enum class PinCut : uint8_t {
	Cut,
	Uncut // leaf pin of a pin ref that a checkpoint with barriers left without a barrier
};

using PinList = std::vector<const Netlist::Pin *>;
using InstanceList = std::vector<const Netlist::Instance *>;

// where an object was at checkpoint, found by netview_ref or barrier id
struct Anchor {
	enum class Role : uint8_t { Pin, Cell, Net, Barrier, Port };
	enum class Side : uint8_t { None, A, Y };

	Role role;
	uint32_t ref_index;              // index into this checkpoint's refs, same in checkpoint and resolve
	std::string scope_path = {};     // with the own scope of the cell or wire
	std::string port = {};
	int bit = 0;
	std::string net_scope_path = {}; // of the scope that holds the wire
	bool in_shared_module = false;
	Side side = Side::None;
	bool uncut = false;              // a leaf pin that got no barrier
};

struct BarrierMarks {
	bool cut_on_a = false;         // the cut wire is on A, at an output
	bool port_cut = false;         // the cut side holds all uses of a port bit
	bool keep_as_instance = false; // a Barrier instance in the view, keeps a hierarchical pin
};

struct TopPortName {
	std::string port;
	int index; // the declared index of the bit
};

// cell names at the checkpoint, until the next one
// a later rename keeps the old scope path
struct Snapshot {
	dict<uint32_t, std::string> cell_names; // by cell hashidx_
	pool<std::string> cell_paths;           // lets resolve() tell new buffers from old cells
public:
	void take(const NetView &view);
	void takeScope(const NetView &view, const Netlist::Instance *scope);
	std::string scopePath(const NetView &view, const Netlist::Instance *scope) const;
	std::string cellScopePath(const NetView &view, const Netlist::Instance *inst) const;
};

struct AnchorStore {
	// by cell or wire netview_ref value, process wide, seeded by keySeed
	dict<int, std::vector<Anchor>> anchors_by_ref_attr;
public:
	void append(RTLIL::Design *design, RTLIL::AttrObject *object, const Anchor &anchor);
	const std::vector<Anchor> &anchorsOf(RTLIL::Design *design, const RTLIL::AttrObject *object) const;
};

// anchors by barrier id and barrier marks
struct BarrierStore {
	// from the last checkpoint
	ListMap<int, Anchor> anchors_by_barrier; // by the barrier id in the barrier name
	pool<const RTLIL::Cell *> anchored_barriers;

	// marks of the current barriers
	dict<int, BarrierMarks> marks_by_barrier;
	// barrier id is the netview_anchor value of a $barrier, process wide
	static inline int last_barrier_id = 0;
public:
	int nextId();
	void skipIdsInUse(RTLIL::Design *design);
	BarrierMarks marks(const RTLIL::Cell *barrier) const;
};

struct TrackData {
	static inline int last_serial = 0;
	static inline pool<int> live_serials;

	Snapshot snapshot;
	AnchorStore anchors;
	BarrierStore barriers;
	ListMap<uint32_t, TopPortName> top_ports_by_ref;
	int serial;
public:
	TrackData();
	~TrackData();
	void bind(RTLIL::Design *design) const;
	void clearAnchors(RTLIL::Design *design);
};

struct AnchorHit {
	Anchor anchor = {};
	const Netlist::Instance *instance = nullptr; // of a cell anchor
	const Netlist::Net *net = nullptr;           // of a wire anchor
	bool in_own_scope = false;
	const RTLIL::Cell *barrier = nullptr;        // of a barrier anchor
	const Netlist::Instance *barrier_scope = nullptr;
};

// finds the anchors in the view in build order
struct HitIndex {
	HitIndex(const NetView &view, const TrackData &data);
	const std::vector<AnchorHit> &hitsOf(uint32_t ref_index) const;
private:
	void noteScope(const Netlist::Instance *scope);
	void noteInstance(const Netlist::Instance *inst);
	void noteBarrier(const RTLIL::Cell *cell, const Netlist::Instance *scope);
	void noteWires(const Netlist::Instance *scope);
	dict<RTLIL::SigBit, const Netlist::Net *> netsOfWireBits(const Netlist::Instance *scope) const;
	void noteWireBit(const Netlist::Net *net, const RTLIL::SigBit &bit);
private:
	const NetView &view_;
	const TrackData &data_;
	Netlist::IdMap<std::vector<AnchorHit>> hits_by_ref_;
};

struct CutSideWalkState {
	const Netlist::Instance *scope;
	Netlist::WalkTarget target;
	BufferRule buffer_rule;
	std::vector<const Netlist::Pin *> &reached_pins;
	pool<const RTLIL::Cell *> visited_cells = {};
};

// walks from a barrier to one side's leaf pins or top ports
// a new buffer is one not in the Snapshot
struct CutSideWalker {
	CutSideWalker(const NetView &view, const TrackData &data);
	void pins(const AnchorHit &hit, Anchor::Side side, BufferRule rule, PinList &out);
private:
	void walkBarrier(CutSideWalkState &walk, const RTLIL::Cell *barrier);
	void walkSignal(CutSideWalkState &walk, const RTLIL::Cell *from, const RTLIL::SigBit &bit, bool on_cut_wire);
	bool entersBarrier(const CutSideWalkState &walk, const ModWalker::PortBit &at, bool on_cut_wire) const;
	void walkUser(CutSideWalkState &walk, const ModWalker::PortBit &at, bool on_cut_wire);
	void walkNewBuffer(CutSideWalkState &walk, const ModWalker::PortBit &at, bool on_cut_wire);
	const Netlist::Pin *topPortPinOf(const RTLIL::SigBit &bit, const ModWalker &walker);
private:
	const NetView &view_;
	const TrackData &data_;
	std::map<RTLIL::Module *, ModWalker> mod_walkers_;
	dict<RTLIL::SigBit, const Netlist::Pin *> top_port_pin_by_bit_; // by top SigMap bit
};

struct AnchorWriter {
	AnchorWriter(const NetView &view, TrackData &data, CutSideWalker &walker);
	void write(uint32_t ref_index, TrackedRef &ref, size_t at, bool with_barriers, PinCut cut);
private:
	void anchorPin(const Netlist::Pin *pin, uint32_t ref_index, TrackedRef &ref, bool with_barriers, PinCut cut);
	void anchorBarrierInstancePin(const Netlist::Pin *pin, uint32_t ref_index, TrackedRef &ref, bool with_barriers);
	void anchorDriversOfBarrierInstance(const Netlist::Pin *pin, uint32_t ref_index, TrackedRef &ref);
	void anchorCell(const Netlist::Instance *inst, Anchor anchor);
	void anchorWires(const Netlist::Net *net, uint32_t ref_index);
	bool markIfShared(RTLIL::AttrObject *object, RTLIL::Module *module);
private:
	const NetView &view_;
	TrackData &data_;
	CutSideWalker &walker_;
};

// puts $barrier cells at the objects of each ref
// a barrier cuts a pin off its net with a cut wire
struct BarrierWriter {
	BarrierWriter(const NetView &view, TrackData &data);
	PinCut protect(uint32_t ref_index, const TrackedRef &ref, size_t at);
	void cutPorts();
	void removeUnusedBarriers();
	bool changedView() const;
private:
	// barrier at the leaf pin, or the port inside a hierarchical pin
	PinCut protectPin(const Netlist::Pin *pin, uint32_t ref_index, const TrackedRef &ref);
	PinCut protectLeafPin(const Netlist::Pin *pin, uint32_t ref_index, const std::string &net_scope_path = "");
	void protectHierPin(const Netlist::Pin *pin, uint32_t ref_index, bool keep_as_instance);
	void protectPort(const Netlist::Pin *pin, uint32_t ref_index); // barrier at a bit of a top bus port
	// barriers at each pin of a gate, the clock pins of a register
	void protectCell(const Netlist::Instance *inst, uint32_t ref_index);
	void protectNet(const Netlist::Net *net, uint32_t ref_index); // barriers at the leaf drivers
	PinCut anchorPinBarrier(const Netlist::Pin *pin, uint32_t ref_index, const std::string &net_scope_path = "");
	PinCut keepUncutPin(const Netlist::Pin *pin);
	RTLIL::Cell *ensureBarrierAtPin(const Netlist::Pin *pin);
	RTLIL::Cell *ensureBarrierAtPort(const Netlist::Pin *pin);
	void noteBarrier(RTLIL::Cell *barrier);
	RTLIL::Cell *useBarrier(RTLIL::Cell *barrier);
	bool isUnusedBarrier(const RTLIL::Cell *cell) const;
	void removeBarrier(RTLIL::Cell *barrier);
	RTLIL::Cell *createBarrierCell(RTLIL::Module *module, const RTLIL::SigBit &a, const RTLIL::SigBit &y, BarrierMarks marks);
	void markWiresKeep(const Netlist::Net *net);
private:
	const NetView &view_;
	TrackData &data_;
	dict<RTLIL::SigBit, RTLIL::Cell *> barrier_by_cut_bit_;
	dict<RTLIL::SigBit, RTLIL::Cell *> port_barrier_by_bit_;
	dict<RTLIL::Module *, dict<RTLIL::SigBit, RTLIL::SigBit>> cut_by_port_bit_;
	pool<const RTLIL::Cell *> new_port_barriers_;
	pool<const RTLIL::Cell *> used_barriers_;
	bool changed_view_ = false;
};

struct LeafCutSides {
	std::vector<const Netlist::Pin *> cut = {};
	std::vector<const Netlist::Pin *> flattened = {};
	std::vector<const Netlist::Pin *> inside = {};
};

struct ResolvedPin {
	std::vector<const Netlist::Pin *> pins = {};
	std::vector<const Netlist::Pin *> own_pins = {};
};

// turns the hits of each ref into objects
struct Resolver {
	Resolver(const NetView &view, const TrackData &data, const HitIndex &hit_index, CutSideWalker &walker);
	void resolve(uint32_t ref_index, TrackedRef &ref);
private:
	std::vector<const Netlist::Pin *> cutSidePinsOfHits(const std::vector<AnchorHit> &hits);
	void collectLoadsBeyondAndBarrierPins(const std::vector<AnchorHit> &hits, TrackedRef &ref);
	ResolvedPin resolvePin(const std::vector<AnchorHit> &hits, const TrackedRef &ref);
	LeafCutSides leafCutSides(const std::vector<AnchorHit> &hits, const InstanceList &hier_insts);
	PinList pinsBehindNewLogic(const InstanceList &insts, const PinList &cut) const;
	void addOutputLoads(const Netlist::Instance *inst, std::vector<const Netlist::Pin *> &loads) const;
	std::vector<const Netlist::Instance *> resolveCell(const std::vector<AnchorHit> &hits);
	std::vector<const Netlist::Pin *> resolvePort(const std::vector<AnchorHit> &hits, uint32_t ref_index);
	void addTopPins(const std::vector<AnchorHit> &hits, uint32_t ref_index, TrackedRef &ref);
	std::vector<const Netlist::Pin *> topPinsOfRef(const std::vector<AnchorHit> &hits, uint32_t ref_index) const;
	std::vector<const Netlist::Pin *> namedTopPins(uint32_t ref_index) const;
	void collectTopPorts(const Netlist::Net *net, std::vector<const Netlist::Pin *> &pins) const;
	PinList checkpointedPorts(const PinList &ports, uint32_t ref_index) const;
	PinList leafPinsUnderScope(const Netlist::Net *net, const std::string &scope_path) const;
	const Netlist::Net *netInScope(const Netlist::Net *net, const std::string &scope_path) const;
	const Netlist::Net *newBufferInput(const Netlist::Net *net) const;
	const Netlist::Net *newBufferRoot(const Netlist::Net *net) const;
	std::vector<const Netlist::Net *> bufferSplitRoots(const pool<const Netlist::Net *> &parts) const;
	std::vector<const Netlist::Net *> resolveNet(const std::vector<AnchorHit> &hits, TrackedRef &ref);
	std::vector<PortRename> portRenames(const std::vector<AnchorHit> &hits, const InstanceList &insts);
private:
	const NetView &view_;
	const TrackData &data_;
	const HitIndex &hit_index_;
	CutSideWalker &walker_;
};

// checkpoint helpers
size_t objectCount(const TrackedRef &ref);
int newRefValue(RTLIL::Design *design);
int keySeed(RTLIL::Design *design);
RTLIL::SigBit portBit(const NetView &view, const Netlist::Pin *pin);

// owned attributes and tracking marks
void ensureScopename(RTLIL::AttrObject *object);
void setOwnedAttribute(RTLIL::Design *design, RTLIL::AttrObject *object, RTLIL::IdString attr);
void removeOwnedKeeps(RTLIL::Design *design);
void removeOwnedAttribute(RTLIL::AttrObject *object, RTLIL::IdString attr, RTLIL::IdString marker);
void removeEmptyScopename(RTLIL::AttrObject *object);
void removeTrackingMarks(RTLIL::Design *design);

// barrier cells, ids and cut wires
RTLIL::Wire *addCutWire(RTLIL::Module *module);
void unmarkCutWire(RTLIL::Wire *wire);
std::optional<int> barrierIdOf(const RTLIL::Cell *barrier);
BarrierMarks writtenMarks(const RTLIL::Cell *barrier);
std::vector<RTLIL::Cell *> barrierCells(RTLIL::Design *design);
RTLIL::Selection trackedBarriers(RTLIL::Design *design);
void recordBarrierAnchor(const NetView &view, BarrierStore &barriers, const RTLIL::Cell *barrier, const std::string &path, Anchor anchor);
void replaceBitsInModule(RTLIL::Module *module, const dict<RTLIL::SigBit, RTLIL::SigBit> &rules, const pool<const RTLIL::Cell *> &skip);

// scope paths of cells, wires and barriers
bool hasOwnScope(const RTLIL::AttrObject *object);
std::vector<std::string> ownScopeParts(const RTLIL::AttrObject *object);
std::string withOwnScope(const std::string &path, const RTLIL::AttrObject *object);
std::string barrierScopePath(const std::string &path, const RTLIL::Cell *barrier);

// resolve helpers
// own-scope hits of role, else all, or none if any is in_shared_module
std::vector<const AnchorHit *> hitsOfRole(const std::vector<AnchorHit> &hits, Anchor::Role role);
PinList hierPinsAbove(const InstanceList &insts, const PinList &leaves, Netlist::PortDir dir);
const Netlist::Pin *findTopPort(const Netlist::Instance *top, const TopPortName &name);
bool isNewBuffer(const NetView &view, const Snapshot &snapshot, const Netlist::Instance *inst);

template <typename T> std::vector<const T *> uniqueSorted(std::vector<const T *> objects)
{
	std::sort(objects.begin(), objects.end(), detail::idLess<T>);
	objects.erase(std::unique(objects.begin(), objects.end()), objects.end());
	return objects;
}

} // namespace detail

YOSYS_NAMESPACE_END

#endif
