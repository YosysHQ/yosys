#include "kernel/netlist.h"

YOSYS_NAMESPACE_BEGIN

bool Netlist::Port::scalar() const { return width == 1 && !vector; }

int Netlist::Port::hdlIndex(int bit) const
{
	if (from < to)
		return to - bit;
	return to + bit;
}

bool Netlist::Instance::isTop() const { return parent == nullptr; }
bool Netlist::Instance::isLeaf() const { return kind == Kind::LibraryCell || kind == Kind::InternalCell; }

Netlist::Pin *Netlist::Instance::findPin(const std::string &port, int bit) const
{
	for (Pin *pin : pins) {
		if (pin->port().name == port && pin->bit == bit)
			return pin;
	}
	return nullptr;
}

const Netlist::Port &Netlist::Pin::port() const { return (*inst->ports)[port_index]; }

Netlist::PortDir Netlist::Pin::dir() const { return port().dir; }

int Netlist::Pin::hdlIndex() const { return port().hdlIndex(bit); }

bool Netlist::Pin::isDriver() const
{
	PortDir d = dir();
	bool output = d == PortDir::Output || d == PortDir::Inout;
	bool input = d == PortDir::Input || d == PortDir::Inout;
	if (inst->isTop())
		return input; // a top input drives the design
	return output && inst->isLeaf();
}

Netlist::PortDir Netlist::portDir(bool input, bool output)
{
	if (input && output)
		return PortDir::Inout;
	if (input)
		return PortDir::Input;
	if (output)
		return PortDir::Output;
	return PortDir::Unknown;
}

YOSYS_NAMESPACE_END
