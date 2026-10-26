#include "kernel/netlist.h"

YOSYS_NAMESPACE_BEGIN

Netlist::PortModel::~PortModel() {}

bool Netlist::Instance::isLeaf() const
{
	return kind == Kind::LibraryLeaf || kind == Kind::InternalLeaf;
}

bool Netlist::PortShape::scalar() const
{
	return width == 1 && !vector;
}

Netlist::Dir Netlist::portDir(bool input, bool output)
{
	if (input && output)
		return Dir::Inout;
	if (input)
		return Dir::Input;
	if (output)
		return Dir::Output;
	return Dir::Unknown;
}

bool Netlist::isTop(const Instance *inst) const
{
	return inst->parent == nullptr;
}

const Netlist::PortShape &Netlist::shape(const Pin *pin) const
{
	return (*pin->inst->ports)[pin->port];
}

Netlist::Dir Netlist::dir(const Pin *pin) const
{
	return shape(pin).dir;
}

int Netlist::hdlIndex(const Pin *pin) const
{
	const PortShape &s = shape(pin);
	if (s.from < s.to)
		return s.to - pin->bit;
	return s.to + pin->bit;
}

bool Netlist::isDriver(const Pin *pin) const
{
	Dir d = dir(pin);
	bool output = d == Dir::Output || d == Dir::Inout;
	bool input = d == Dir::Input || d == Dir::Inout;
	if (isTop(pin->inst))
		return input; // a top input drives the design
	return output && pin->inst->isLeaf();
}

YOSYS_NAMESPACE_END
