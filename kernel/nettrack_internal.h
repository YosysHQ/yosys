#ifndef NETTRACK_INTERNAL_H
#define NETTRACK_INTERNAL_H

#include "kernel/nettrack.h"
#include "kernel/netview_internal.h"

#include <string_view>

YOSYS_NAMESPACE_BEGIN

namespace detail
{

constexpr std::string_view ref_attr = "\\netview_ref";

enum class IdLookup : uint8_t { FindOnly, AddIfMissing };

struct Anchor {
	enum class Role : uint8_t { Pin, Cell, Net };

	Role role;
	uint32_t ref_index;
	std::string scope_path; // with the own scope of the cell or wire
	std::string port;
	int bit;
	std::string net_scope_path; // of the scope that holds the wire
	bool in_shared_module;
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

struct TrackData {
	Snapshot snapshot;
	AnchorStore anchors;
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

// Attributes
void ensureScopename(RTLIL::AttrObject *object);

// Scope paths
bool hasOwnScope(const RTLIL::AttrObject *object);
std::vector<std::string> ownScopeParts(const RTLIL::AttrObject *object);
std::string withOwnScope(const std::string &path, const RTLIL::AttrObject *object);

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
