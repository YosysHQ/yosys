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

enum class IdLookup : uint8_t { FindOnly, AddIfMissing };

enum class BufferRule : uint8_t { StopAtNewBuffer, PassNewBuffer };

struct Anchor {
	enum class Role : uint8_t { Pin, Cell, Net, Barrier };
	enum class Side : uint8_t { None, A, Y };

	Role role;
	uint32_t ref_index;
	std::string scope_path; // with the own scope of the cell or wire
	std::string port;
	int bit;
	std::string net_scope_path; // of the scope that holds the wire
	bool in_shared_module;
	Side side = Side::None;
	bool uncut = false; // a leaf pin that got no barrier
};

struct BarrierMarks {
	bool cut_on_a = false;	       // the cut wire is on A, at an output
	bool port_cut = false;	       // the cut side holds all uses of a port bit
	bool keep_as_instance = false; // a Barrier instance in the view, keeps a hierarchical pin
};

struct TopPortName {
	std::string port;
	int index; // the declared index of the bit
};

struct Snapshot {
	dict<uint32_t, std::string> cell_names; // by cell hashidx_
	pool<std::string> cell_paths;
public:
	void take(const NetView &view);
	void takeScope(const NetView &view, const Netlist::Instance *scope);
	void clear();
	std::string scopePath(const NetView &view, const Netlist::Instance *scope) const;
	std::string cellScopePath(const NetView &view, const Netlist::Instance *inst) const;
};

struct AnchorStore {
	dict<int, std::vector<Anchor>> anchors_by_ref_attr; // by attribute value
public:
	void append(RTLIL::Design *design, RTLIL::AttrObject *object, const Anchor &anchor);
	const std::vector<Anchor> &anchorsOf(RTLIL::Design *design, const RTLIL::AttrObject *object) const;
	void markUncut(RTLIL::Design *design, const RTLIL::AttrObject *object, uint32_t ref_index, const Netlist::Pin *pin);
	void clear();
};

struct BarrierStore {
	ListMap<int, Anchor> anchors_by_barrier;
	pool<const RTLIL::Cell *> anchored_barriers;
	dict<int, BarrierMarks> marks_by_barrier;
	int last_barrier_id = 0;
public:
	int nextId();
	void skipIdsInUse(RTLIL::Design *design);
	BarrierMarks marks(const RTLIL::Cell *barrier) const;
	void setMarks(const RTLIL::Cell *barrier, const BarrierMarks &marks);
	RTLIL::IdString cutPort(const RTLIL::Cell *barrier) const;
	void clearMarks();
	void clearAnchors();
};

struct TrackData {
	Snapshot snapshot;
	AnchorStore anchors;
	BarrierStore barriers;
	ListMap<uint32_t, TopPortName> top_ports_by_ref;
	int serial;
	static inline int last_serial = 0;
	static inline pool<int> live_serials;
public:
	TrackData();
	~TrackData();
	void bind(RTLIL::Design *design) const;
	void clearAnchors(RTLIL::Design *design);
};

struct AnchorHit {
	Anchor anchor;
	const Netlist::Instance *instance; // of a cell anchor
	const Netlist::Net *net;	         // of a wire anchor
	bool in_own_scope;
	const RTLIL::Cell *barrier = nullptr; // of a barrier anchor
	const Netlist::Instance *barrier_scope = nullptr;
};

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

struct CutSideWalker {
	CutSideWalker(const NetView &view, const TrackData &data);
	void pins(const RTLIL::Cell *barrier, const Netlist::Instance *scope, Anchor::Side side, BufferRule rule, std::vector<const Netlist::Pin *> &out);
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
	void write(uint32_t ref_index, TrackedRef &ref, size_t at, TrackMode mode);
private:
	void anchorPin(const Netlist::Pin *pin, uint32_t ref_index, TrackedRef &ref, TrackMode mode);
	void anchorBarrierInstancePin(const Netlist::Pin *pin, uint32_t ref_index, TrackedRef &ref, TrackMode mode);
	void anchorDriversOfBarrierInstance(const Netlist::Pin *pin, uint32_t ref_index, TrackedRef &ref);
	void anchorCell(const Netlist::Instance *inst, Anchor anchor);
	void anchorWires(const Netlist::Net *net, uint32_t ref_index);
	bool markIfShared(RTLIL::AttrObject *object, RTLIL::Module *module);
private:
	const NetView &view_;
	TrackData &data_;
	CutSideWalker &walker_;
};

struct BarrierWriter {
	BarrierWriter(const NetView &view, TrackData &data);
	void protect(uint32_t ref_index, const TrackedRef &ref, size_t at);
	bool madeNewBarrierInstance() const;
private:
	void protectPin(const Netlist::Pin *pin, uint32_t ref_index, const TrackedRef &ref);
	void protectLeafPin(const Netlist::Pin *pin, uint32_t ref_index, const std::string &net_scope_path = "");
	void protectHierPin(const Netlist::Pin *pin, uint32_t ref_index, bool keep_as_instance);
	void protectPort(const Netlist::Pin *pin, uint32_t ref_index);
	void protectCell(const Netlist::Instance *inst, uint32_t ref_index);
	void protectNet(const Netlist::Net *net, uint32_t ref_index);
	void isolateCell(const Netlist::Instance *inst);
	void anchorPinBarrier(const Netlist::Pin *pin, uint32_t ref_index, const std::string &net_scope_path = "");
	void keepUncutPin(const Netlist::Pin *pin, uint32_t ref_index);
	RTLIL::Cell *ensureBarrierAtPin(const Netlist::Pin *pin);
	RTLIL::Cell *ensureBarrierAtPort(const Netlist::Pin *pin);
	RTLIL::Cell *findPortBarrier(RTLIL::Module *module, const RTLIL::SigBit &bit) const;
	RTLIL::Cell *createBarrierCell(RTLIL::Module *module, const RTLIL::SigBit &a, const RTLIL::SigBit &y, const BarrierMarks &marks);
	void markWiresKeep(const Netlist::Net *net);
	void collectLeafDrivers(const Netlist::Net *net, pool<const Netlist::Net *> &seen, std::vector<const Netlist::Pin *> &drivers) const;
private:
	const NetView &view_;
	TrackData &data_;
	dict<RTLIL::SigBit, RTLIL::Cell *> barrier_by_cut_bit_;
	bool made_new_barrier_instance_ = false; // the view changed
};

struct Resolver {
	Resolver(const NetView &view, const TrackData &data, const HitIndex &hit_index, CutSideWalker &walker);
	void resolve(uint32_t ref_index, TrackedRef &ref);
private:
	std::vector<const Netlist::Pin *> cutSidePinsOfHits(const std::vector<AnchorHit> &hits, BufferRule rule);
	void collectLoadsBeyondAndBarrierPins(const std::vector<AnchorHit> &hits, TrackedRef &ref);
	std::vector<const Netlist::Pin *> resolvePin(const std::vector<AnchorHit> &hits, TrackedRef &ref);
	std::vector<const Netlist::Pin *> pinsBehindNewLogic(const std::vector<const Netlist::Instance *> &insts, const std::vector<const Netlist::Pin *> &cut) const;
	void addOutputLoads(const Netlist::Instance *inst, std::vector<const Netlist::Pin *> &loads) const;
	std::vector<const Netlist::Instance *> resolveCell(const std::vector<AnchorHit> &hits);
	std::vector<const Netlist::Pin *> resolvePort(const std::vector<AnchorHit> &hits, uint32_t ref_index);
	std::vector<const Netlist::Pin *> namedTopPins(uint32_t ref_index) const;
	void collectTopPorts(const Netlist::Net *net, std::vector<const Netlist::Pin *> &pins) const;
	std::vector<const Netlist::Pin *> leafPinsUnderScope(const Netlist::Net *net, const std::string &scope_path) const;
	const Netlist::Net *netInScope(const Netlist::Net *net, const std::string &scope_path) const;
	const Netlist::Net *newBufferInput(const Netlist::Net *net) const;
	const Netlist::Net *newBufferRoot(const Netlist::Net *net) const;
	std::vector<const Netlist::Net *> bufferSplitRoots(const pool<const Netlist::Net *> &parts) const;
	std::vector<const Netlist::Net *> resolveNet(const std::vector<AnchorHit> &hits, TrackedRef &ref);
	std::vector<PortRename> portRenames(const std::vector<AnchorHit> &hits, const std::vector<const Netlist::Instance *> &insts);
private:
	const NetView &view_;
	const TrackData &data_;
	const HitIndex &hit_index_;
	CutSideWalker &walker_;
};

// Checkpoint
size_t objectCount(const TrackedRef &ref);
int newRefValue(RTLIL::Design *design);
int keySeed(RTLIL::Design *design);

// Ids
RTLIL::IdString attrId(RTLIL::Design *design, std::string_view name, IdLookup lookup);
RTLIL::IdString refAttrId(RTLIL::Design *design, IdLookup lookup);
RTLIL::IdString ownedMarkerId(RTLIL::Design *design, RTLIL::IdString attr, IdLookup lookup);

// Attributes
void ensureScopename(RTLIL::AttrObject *object);
void setOwnedAttribute(RTLIL::Design *design, RTLIL::AttrObject *object, RTLIL::IdString attr);
void removeOwnedMarks(RTLIL::Design *design, RTLIL::AttrObject *object);
void removeTrackingMarks(RTLIL::Design *design);

// Barriers
RTLIL::Wire *addCutWire(RTLIL::Module *module);
std::optional<int> barrierIdOf(const RTLIL::Cell *barrier);
BarrierMarks writtenMarks(const RTLIL::Cell *barrier);
RTLIL::Selection trackedBarriers(RTLIL::Design *design);
void recordBarrierAnchor(const NetView &view, BarrierStore &barriers, const RTLIL::Cell *barrier, const std::string &path, Anchor anchor);
void replaceBitInModule(RTLIL::Module *module, const RTLIL::SigBit &bit, const RTLIL::SigBit &other);
RTLIL::IdString barrierPortToward(Netlist::WalkTarget target);

// Scope paths
bool hasOwnScope(const RTLIL::AttrObject *object);
std::vector<std::string> ownScopeParts(const RTLIL::AttrObject *object);
std::string withOwnScope(const std::string &path, const RTLIL::AttrObject *object);
std::string barrierScopePath(const std::string &path, const RTLIL::Cell *barrier);

// Resolve
std::vector<const AnchorHit *> hitsOfRole(const std::vector<AnchorHit> &hits, Anchor::Role role);
std::vector<const Netlist::Pin *> hierPinsAbove(const std::vector<const Netlist::Instance *> &insts, const std::vector<const Netlist::Pin *> &leaves);
const Netlist::Pin *findTopPort(const Netlist::Instance *top, const TopPortName &name);
bool isNewBuffer(const NetView &view, const Snapshot &snapshot, const Netlist::Instance *inst);

template <typename T> std::vector<T> uniqueSorted(std::vector<T> objects)
{
	std::sort(objects.begin(), objects.end());
	objects.erase(std::unique(objects.begin(), objects.end()), objects.end());
	return objects;
}

} // namespace detail

YOSYS_NAMESPACE_END

#endif
