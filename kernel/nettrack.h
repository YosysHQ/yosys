// NetTracker lets refs find objects again after passes change the design

#ifndef NETTRACK_H
#define NETTRACK_H

#include "kernel/netview.h"

YOSYS_NAMESPACE_BEGIN

namespace detail
{
struct TrackData;
}

// the caller fills kind and the list of that kind, resolve refills the lists
struct TrackedRef {
	enum class Kind : uint8_t { Pin, Instance, Net };

	struct PortCut {
		std::string port;
		bool is_output;
		Netlist::PinList pins; // now at its cut side, the loads behind an output with no new driver
	};

	Kind kind;                            // resolve makes a Net that is gone a Pin of the leaf pins that were on it
	Netlist::PinList pins = {};           // a resolved leaf pin is on its cut side
	Netlist::InstanceList instances = {}; // when the cell is gone, the cells between its barriers
	bool gone = false;                    // resolve did not find the object
	// the loads behind a leaf Pin or an Instance that is a wire or a constant now, a checkpoint anchors them as pins
	Netlist::PinList loads = {};
	std::vector<PortCut> port_cuts = {}; // each old port of an Instance
	Netlist::NetList nets = {};
};

// checkpoint -> passes -> new view -> resolve
// one tracker per design and one thread, not checked
// a checkpoint leaves a netview_ref id and an hdlname in the design, on each scope cell and each ref object
struct NetTracker final {
	NetTracker();
	~NetTracker();

	// drops the old anchors, the view must be up to date
	// protect puts a $barrier at each ref pin and a keep on each ref cell, without it a pass can remove the object
	void checkpoint(NetView &view, const std::vector<TrackedRef *> &refs, bool protect = true);
	// takes the refs of the checkpoint in the same order, can rerun
	// two moved cells that fit one ref lose it, a copy can get the ref of a deleted cell
	void resolve(const NetView &view, const std::vector<TrackedRef *> &refs);
	// drops the ids and the anchors, barriers stay until unprotect
	void clear(RTLIL::Design *design);
	// removes barriers and keeps, the anchors stay, a later checkpoint needs protect = false
	void unprotect(RTLIL::Design *design);
private:
	std::unique_ptr<detail::TrackData> data_;
};

YOSYS_NAMESPACE_END

#endif
