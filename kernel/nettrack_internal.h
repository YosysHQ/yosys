#ifndef NETTRACK_INTERNAL_H
#define NETTRACK_INTERNAL_H

#include "kernel/nettrack.h"
#include "kernel/netview_internal.h"

#include <optional>
#include <string_view>

YOSYS_NAMESPACE_BEGIN

namespace detail
{

constexpr std::string_view anchor_prefix = "netview_anchor";
constexpr std::string_view anchor_attr = "\\netview_anchor";
constexpr std::string_view ref_attr = "\\netview_ref";
constexpr std::string_view owned_marker_prefix = "\\netview_";

enum class IdLookup : uint8_t { FindOnly, AddIfMissing };

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
public:
	void take(const NetView &view);
	void takeScope(const NetView &view, const Netlist::Instance *scope);
	void clear();
	std::string scopePath(const NetView &view, const Netlist::Instance *scope) const;
	std::string cellScopePath(const NetView &view, const Netlist::Instance *inst) const;
};

struct AnchorStore {
	std::vector<std::vector<Anchor>> anchors_by_ref_attr;
public:
	void append(RTLIL::Design *design, RTLIL::AttrObject *object, const Anchor &anchor);
	const std::vector<Anchor> &anchorsOf(RTLIL::Design *design, const RTLIL::AttrObject *object) const;
	void clear();
};

struct BarrierStore {
	ListMap<int, Anchor> anchors_by_barrier;
	dict<int, BarrierMarks> marks_by_barrier;
	int last_barrier_id = 0;
public:
	int nextId();
	BarrierMarks marks(const RTLIL::Cell *barrier) const;
	void setMarks(const RTLIL::Cell *barrier, const BarrierMarks &marks);
	RTLIL::IdString cutPort(const RTLIL::Cell *barrier) const;
	void clearAnchors();
};

struct TrackData {
	Snapshot snapshot;
	AnchorStore anchors;
	BarrierStore barriers;
	ListMap<uint32_t, TopPortName> top_ports_by_ref;
public:
	void clearAnchors(RTLIL::Design *design);
};

struct AnchorHit {
	Anchor anchor;
	const Netlist::Instance *instance; // of a cell anchor
	const Netlist::Net *net;	         // of a wire anchor
	bool in_own_scope;
};

struct HitIndex {
	HitIndex(const NetView &view, const TrackData &data);
	const std::vector<AnchorHit> &hitsOf(uint32_t ref_index) const;
private:
	void noteScope(const Netlist::Instance *scope);
	void noteInstance(const Netlist::Instance *inst);
	void noteWires(const Netlist::Instance *scope);
	dict<RTLIL::SigBit, const Netlist::Net *> netsOfWireBits(const Netlist::Instance *scope) const;
	void noteWireBit(const Netlist::Net *net, const RTLIL::SigBit &bit);
private:
	const NetView &view_;
	const TrackData &data_;
	Netlist::IdMap<std::vector<AnchorHit>> hits_by_ref_;
};

struct AnchorWriter {
	AnchorWriter(const NetView &view, TrackData &data);
	void write(uint32_t ref_index, TrackedRef &ref, size_t at);
private:
	void anchorPin(const Netlist::Pin *pin, uint32_t ref_index);
	void anchorCell(const Netlist::Instance *inst, Anchor anchor);
	void anchorWires(const Netlist::Net *net, uint32_t ref_index);
	bool markIfShared(RTLIL::AttrObject *object, RTLIL::Module *module);
private:
	const NetView &view_;
	TrackData &data_;
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
	Resolver(const NetView &view, const TrackData &data, const HitIndex &hit_index);
	void resolve(uint32_t ref_index, TrackedRef &ref);
private:
	std::vector<const Netlist::Pin *> resolvePin(const std::vector<AnchorHit> &hits);
	std::vector<const Netlist::Instance *> resolveCell(const std::vector<AnchorHit> &hits);
	std::vector<const Netlist::Pin *> resolvePort(const std::vector<AnchorHit> &hits, uint32_t ref_index);
	std::vector<const Netlist::Pin *> namedTopPins(uint32_t ref_index) const;
	void collectTopPorts(const Netlist::Net *net, std::vector<const Netlist::Pin *> &pins) const;
	std::vector<const Netlist::Pin *> leafPinsUnderScope(const Netlist::Net *net, const std::string &scope_path) const;
	std::vector<const Netlist::Net *> resolveNet(const std::vector<AnchorHit> &hits, TrackedRef &ref);
private:
	const NetView &view_;
	const TrackData &data_;
	const HitIndex &hit_index_;
};

// Checkpoint
size_t objectCount(const TrackedRef &ref);

// Ids
RTLIL::IdString attrId(RTLIL::Design *design, std::string_view name, IdLookup lookup);
RTLIL::IdString refAttrId(RTLIL::Design *design, IdLookup lookup);
RTLIL::IdString ownedMarkerId(RTLIL::Design *design, RTLIL::IdString attr, IdLookup lookup);

// Attributes
void ensureScopename(RTLIL::AttrObject *object);
void setOwnedAttribute(RTLIL::Design *design, RTLIL::AttrObject *object, RTLIL::IdString attr);

// Barriers
RTLIL::Wire *addCutWire(RTLIL::Module *module);
std::optional<int> barrierIdOf(const RTLIL::Cell *barrier);
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
const Netlist::Pin *findTopPort(const Netlist::Instance *top, const TopPortName &name);

template <typename T> std::vector<T> uniqueSorted(std::vector<T> objects)
{
	std::sort(objects.begin(), objects.end());
	objects.erase(std::unique(objects.begin(), objects.end()), objects.end());
	return objects;
}

} // namespace detail

YOSYS_NAMESPACE_END

#endif
