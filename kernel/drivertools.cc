/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2024  Jannis Harder <jix@yosyshq.com> <me@jix.one>
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */

#include "kernel/drivertools.h"

YOSYS_NAMESPACE_BEGIN

DriveBitWire::DriveBitWire(Wire *wire, int offset) : wire(wire), offset(offset) {}

bool DriveBitWire::operator==(const DriveBitWire &other) const
{
  return wire == other.wire && offset == other.offset;
}

bool DriveBitWire::operator<(const DriveBitWire &other) const
{
  if (wire != other.wire)
    return wire->name < other.wire->name;
  return offset < other.offset;
}

unsigned int DriveBitWire::hash() const
{
  return mkhash_add(wire->name.hash(), offset);
}

DriveBitWire::operator SigBit() const
{
  return SigBit(wire, offset);
}

DriveBitPort::DriveBitPort(Cell *cell, IdString port, int offset)
  : cell(cell), port(port), offset(offset) {}

bool DriveBitPort::operator==(const DriveBitPort &other) const
{
  return cell == other.cell && port == other.port && offset == other.offset;
}

bool DriveBitPort::operator<(const DriveBitPort &other) const
{
  if (cell != other.cell)
    return cell->name < other.cell->name;
  if (port != other.port)
    return port < other.port;
  return offset < other.offset;
}

unsigned int DriveBitPort::hash() const
{
  return mkhash_add(mkhash(cell->name.hash(), port.hash()), offset);
}

DriveBitMarker::DriveBitMarker(int marker, int offset) : marker(marker), offset(offset) {}

bool DriveBitMarker::operator==(const DriveBitMarker &other) const
{
  return marker == other.marker && offset == other.offset;
}

bool DriveBitMarker::operator<(const DriveBitMarker &other) const
{
  if (marker != other.marker)
    return marker < other.marker;
  return offset < other.offset;
}

unsigned int DriveBitMarker::hash() const
{
  return mkhash_add(marker, offset);
}

DriveBit::DriveBit(SigBit const &bit)
{
  if (bit.is_wire())
    *this = DriveBitWire(bit.wire, bit.offset);
  else
    *this = bit.data;
}

void DriveBit::merge(DriveBit const &other)
{
  if (other.type_ == DriveType::NONE)
    return;
  if (type_ == DriveType::NONE) {
    *this = other;
    return;
  }
  if (type_ != DriveType::MULTIPLE) {
    DriveBitMultiple multi(std::move(*this));
    *this = std::move(multi);
  }
  multiple().merge(other);
}

DriveBitMultiple::DriveBitMultiple() {}

DriveBitMultiple::DriveBitMultiple(DriveBit const &single)
{
    multiple_.emplace(single);
}

pool<DriveBit> const &DriveBitMultiple::multiple() const
{
    return multiple_;
}

void DriveBitMultiple::merge(DriveBitMultiple const &other)
{
    for (DriveBit const &single : other.multiple_)
        merge(single);
}

void DriveBitMultiple::merge(DriveBitMultiple &&other)
{
    for (DriveBit &single : other.multiple_)
        merge(std::move(single));
}

void DriveBitMultiple::merge(DriveBit const &single)
{
    multiple_.emplace(single);
}

void DriveBitMultiple::merge(DriveBit &&single)
{
    multiple_.emplace(std::move(single));
}

bool DriveBitMultiple::operator==(const DriveBitMultiple &other) const
{
    return multiple_ == other.multiple_;
}

unsigned int DriveBitMultiple::hash() const
{
    return multiple_.hash();
}

DriveBit::DriveBit() {}

DriveBit::DriveBit(DriveBit const &other)
{
    *this = other;
}

DriveBit::DriveBit(DriveBit &&other)
{
    *this = std::move(other);
}

DriveBit::DriveBit(State constant)
{
    *this = constant;
}

DriveBit::DriveBit(DriveBitWire const &wire)
{
    *this = wire;
}

DriveBit::DriveBit(DriveBitWire &&wire)
{
    *this = std::move(wire);
}

DriveBit::DriveBit(DriveBitPort const &port)
{
    *this = port;
}

DriveBit::DriveBit(DriveBitPort &&port)
{
    *this = std::move(port);
}

DriveBit::DriveBit(DriveBitMarker const &marker)
{
    *this = marker;
}

DriveBit::DriveBit(DriveBitMarker &&marker)
{
    *this = std::move(marker);
}

DriveBit::DriveBit(DriveBitMultiple const &multiple)
{
    *this = multiple;
}

DriveBit::DriveBit(DriveBitMultiple &&multiple)
{
    *this = std::move(multiple);
}

DriveBit::~DriveBit()
{
    set_none();
}

void DriveBit::set_none()
{
    switch (type_)
    {
        case DriveType::NONE:
            break;
        case DriveType::CONSTANT:
            break;
        case DriveType::WIRE:
            wire_.~DriveBitWire();
            break;
        case DriveType::PORT:
            port_.~DriveBitPort();
            break;
        case DriveType::MARKER:
            marker_.~DriveBitMarker();
            break;
        case DriveType::MULTIPLE:
            multiple_.~DriveBitMultiple();
            break;
    }
    type_ = DriveType::NONE;
}

DriveBit &DriveBit::operator=(DriveBit const &other)
{
    switch (other.type_)
    {
        case DriveType::NONE:
            set_none();
            break;
        case DriveType::CONSTANT:
            *this = other.constant_;
            break;
        case DriveType::WIRE:
            *this = other.wire_;
            break;
        case DriveType::PORT:
            *this = other.port_;
            break;
        case DriveType::MARKER:
            *this = other.marker_;
            break;
        case DriveType::MULTIPLE:
            *this = other.multiple_;
            break;
    }
    return *this;
}

DriveBit &DriveBit::operator=(DriveBit &&other)
{
    switch (other.type_)
    {
        case DriveType::NONE:
            set_none();
            break;
        case DriveType::CONSTANT:
            *this = std::move(other.constant_);
            break;
        case DriveType::WIRE:
            *this = std::move(other.wire_);
            break;
        case DriveType::PORT:
            *this = std::move(other.port_);
            break;
        case DriveType::MARKER:
            *this = std::move(other.marker_);
            break;
        case DriveType::MULTIPLE:
            *this = std::move(other.multiple_);
            break;
    }
    return *this;
}

DriveBit &DriveBit::operator=(State constant)
{
    set_none();
    constant_ = constant;
    type_ = DriveType::CONSTANT;
    return *this;
}

DriveBit &DriveBit::operator=(DriveBitWire const &wire)
{
    set_none();
    new (&wire_) DriveBitWire(wire);
    type_ = DriveType::WIRE;
    return *this;
}

DriveBit &DriveBit::operator=(DriveBitWire &&wire)
{
    set_none();
    new (&wire_) DriveBitWire(std::move(wire));
    type_ = DriveType::WIRE;
    return *this;
}

DriveBit &DriveBit::operator=(DriveBitPort const &port)
{
    set_none();
    new (&port_) DriveBitPort(port);
    type_ = DriveType::PORT;
    return *this;
}

DriveBit &DriveBit::operator=(DriveBitPort &&port)
{
    set_none();
    new (&port_) DriveBitPort(std::move(port));
    type_ = DriveType::PORT;
    return *this;
}

DriveBit &DriveBit::operator=(DriveBitMarker const &marker)
{
    set_none();
    new (&marker_) DriveBitMarker(marker);
    type_ = DriveType::MARKER;
    return *this;
}

DriveBit &DriveBit::operator=(DriveBitMarker &&marker)
{
    set_none();
    new (&marker_) DriveBitMarker(std::move(marker));
    type_ = DriveType::MARKER;
    return *this;
}

DriveBit &DriveBit::operator=(DriveBitMultiple const &multiple)
{
    set_none();
    if (multiple.multiple().empty())
        return *this;
    new (&multiple_) DriveBitMultiple(multiple);
    type_ = DriveType::MULTIPLE;
    return *this;
}

DriveBit &DriveBit::operator=(DriveBitMultiple &&multiple)
{
    set_none();
    if (multiple.multiple().empty())
        return *this;
    new (&multiple_) DriveBitMultiple(std::move(multiple));
    type_ = DriveType::MULTIPLE;
    return *this;
}

unsigned int DriveBit::hash() const
{
    unsigned int inner;
    switch (type_)
    {
        case DriveType::NONE:
            inner = 0;
            break;
        case DriveType::CONSTANT:
            inner = constant_;
            break;
        case DriveType::WIRE:
            inner = wire_.hash();
            break;
        case DriveType::PORT:
            inner = port_.hash();
            break;
        case DriveType::MARKER:
            inner = marker_.hash();
            break;
        case DriveType::MULTIPLE:
            inner = multiple_.hash();
            break;
    }
    return mkhash((unsigned int)type_, inner);
}

bool DriveBit::operator==(const DriveBit &other) const
{
    if (type_ != other.type_)
        return false;

    switch (type_)
    {
        case DriveType::NONE:
            return true;
        case DriveType::CONSTANT:
            return constant_ == other.constant_;
        case DriveType::WIRE:
            return wire_ == other.wire_;
        case DriveType::PORT:
            return port_ == other.port_;
        case DriveType::MARKER:
            return marker_ == other.marker_;
        case DriveType::MULTIPLE:
            return multiple_ == other.multiple_;
    }
    log_assert(false);
}

bool DriveBit::operator!=(const DriveBit &other) const
{
    return !(*this == other);
}

bool DriveBit::operator<(const DriveBit &other) const
{
    if (type_ != other.type_)
        return type_ < other.type_;
    switch (type_)
    {
        case DriveType::NONE:
            return false;
        case DriveType::CONSTANT:
            return constant_ < other.constant_;
        case DriveType::WIRE:
            return wire_ < other.wire_;
        case DriveType::PORT:
            return port_ < other.port_;
        case DriveType::MARKER:
            return marker_ < other.marker_;
        case DriveType::MULTIPLE:
            log_assert(!"TODO");
    }
    log_abort();
}

DriveType DriveBit::type() const
{
    return type_;
}

bool DriveBit::is_none() const
{
    return type_ == DriveType::NONE;
}

bool DriveBit::is_constant() const
{
    return type_ == DriveType::CONSTANT;
}

bool DriveBit::is_wire() const
{
    return type_ == DriveType::WIRE;
}

bool DriveBit::is_port() const
{
    return type_ == DriveType::PORT;
}

bool DriveBit::is_marker() const
{
    return type_ == DriveType::MARKER;
}

bool DriveBit::is_multiple() const
{
    return type_ == DriveType::MULTIPLE;
}

State &DriveBit::constant()
{
    log_assert(is_constant());
    return constant_;
}

State const &DriveBit::constant() const
{
    log_assert(is_constant());
    return constant_;
}

DriveBitWire &DriveBit::wire()
{
    log_assert(is_wire());
    return wire_;
}

DriveBitWire const &DriveBit::wire() const
{
    log_assert(is_wire());
    return wire_;
}

DriveBitPort &DriveBit::port()
{
    log_assert(is_port());
    return port_;
}

DriveBitPort const &DriveBit::port() const
{
    log_assert(is_port());
    return port_;
}

DriveBitMarker &DriveBit::marker()
{
    log_assert(is_marker());
    return marker_;
}

DriveBitMarker const &DriveBit::marker() const
{
    log_assert(is_marker());
    return marker_;
}

DriveBitMultiple &DriveBit::multiple()
{
    log_assert(is_multiple());
    return multiple_;
}

DriveBitMultiple const &DriveBit::multiple() const
{
    log_assert(is_multiple());
    return multiple_;
}

DriveBitMultiple DriveChunkMultiple::operator[](int i) const
{
  DriveBitMultiple result;
  for (auto const &single : multiple_)
    result.merge(single[i]);
  return result;
}

DriveChunkWire::DriveChunkWire(Wire *wire, int offset, int width)
    : wire(wire), offset(offset), width(width) {}

DriveChunkWire::DriveChunkWire(DriveBitWire const &bit)
    : wire(bit.wire), offset(bit.offset), width(1) {}

int DriveChunkWire::size() const { return width; }

DriveBitWire DriveChunkWire::operator[](int i) const
{
    log_assert(i >= 0 && i < width);
    return DriveBitWire(wire, offset + i);
}

bool DriveChunkWire::is_whole() const
{
    return offset == 0 && width == wire->width;
}

bool DriveChunkWire::operator==(const DriveChunkWire &other) const
{
    return wire == other.wire && offset == other.offset && width == other.width;
}

bool DriveChunkWire::operator<(const DriveChunkWire &other) const
{
    if (wire != other.wire)
        return wire->name < other.wire->name;
    if (width != other.width)
        return width < other.width;
    return offset < other.offset;
}

unsigned int DriveChunkWire::hash() const
{
    return mkhash_add(mkhash(wire->name.hash(), width), offset);
}

DriveChunkWire::operator SigChunk() const
{
    return SigChunk(wire, offset, width);
}

bool DriveChunkWire::can_append(DriveBitWire const &bit) const
{
  return bit.wire == wire && bit.offset == offset + width;
}



bool DriveChunkWire::try_append(DriveBitWire const &bit)
{
  if (!can_append(bit))
    return false;
  width += 1;
  return true;
}

bool DriveChunkWire::try_append(DriveChunkWire const &chunk)
{
  if (chunk.wire != wire || chunk.offset != offset + width)
    return false;
  width += chunk.width;
  return true;
}



bool DriveChunkPort::can_append(DriveBitPort const &bit) const
{
  return bit.cell == cell && bit.port == port && bit.offset == offset + width;
}

bool DriveChunkPort::try_append(DriveBitPort const &bit)
{
  if (!can_append(bit))
    return false;
  width += 1;
  return true;
}

bool DriveChunkPort::try_append(DriveChunkPort const &chunk)
{
  if (chunk.cell != cell || chunk.port != port || chunk.offset != offset + width)
    return false;
  width += chunk.width;
  return true;
}

DriveChunkPort::DriveChunkPort(Cell *cell, IdString port, int offset, int width)
    : cell(cell), port(port), offset(offset), width(width) {}

DriveChunkPort::DriveChunkPort(Cell *cell, IdString port)
    : cell(cell), port(port), offset(0), width(GetSize(cell->connections().at(port))) {}

DriveChunkPort::DriveChunkPort(Cell *cell, std::pair<IdString, SigSpec> const &conn)
    : cell(cell), port(conn.first), offset(0), width(GetSize(conn.second)) {}

DriveChunkPort::DriveChunkPort(DriveBitPort const &bit)
    : cell(bit.cell), port(bit.port), offset(bit.offset), width(1) {}

int DriveChunkPort::size() const { return width; }

DriveBitPort DriveChunkPort::operator[](int i) const
{
    log_assert(i >= 0 && i < width);
    return DriveBitPort(cell, port, offset + i);
}

bool DriveChunkPort::is_whole() const
{
    return offset == 0 && width == cell->connections().at(port).size();
}

bool DriveChunkPort::operator==(const DriveChunkPort &other) const
{
    return cell == other.cell && port == other.port && offset == other.offset && width == other.width;
}

bool DriveChunkPort::operator<(const DriveChunkPort &other) const
{
    if (cell != other.cell)
        return cell->name < other.cell->name;
    if (port != other.port)
        return port < other.port;
    if (width != other.width)
        return width < other.width;
    return offset < other.offset;
}

unsigned int DriveChunkPort::hash() const
{
    return mkhash_add(mkhash(mkhash(cell->name.hash(), port.hash()), width), offset);
}

bool DriveChunkMarker::can_append(DriveBitMarker const &bit) const
{
  return bit.marker == marker && bit.offset == offset + width;
}

bool DriveChunkMarker::try_append(DriveBitMarker const &bit)
{
  if (!can_append(bit))
    return false;
  width += 1;
  return true;
}

bool DriveChunkMarker::try_append(DriveChunkMarker const &chunk)
{
  if (chunk.marker != marker || chunk.offset != offset + width)
    return false;
  width += chunk.width;
  return true;
}

DriveChunkMarker::DriveChunkMarker(int marker, int offset, int width)
    : marker(marker), offset(offset), width(width) {}

DriveChunkMarker::DriveChunkMarker(DriveBitMarker const &bit)
    : marker(bit.marker), offset(bit.offset), width(1) {}

int DriveChunkMarker::size() const { return width; }

DriveBitMarker DriveChunkMarker::operator[](int i) const
{
    log_assert(i >= 0 && i < width);
    return DriveBitMarker(marker, offset + i);
}

bool DriveChunkMarker::operator==(const DriveChunkMarker &other) const
{
    return marker == other.marker && offset == other.offset && width == other.width;
}

bool DriveChunkMarker::operator<(const DriveChunkMarker &other) const
{
    if (marker != other.marker)
        return marker < other.marker;
    if (width != other.width)
        return width < other.width;
    return offset < other.offset;
}

unsigned int DriveChunkMarker::hash() const
{
    return mkhash_add(mkhash(marker, width), offset);
}

bool DriveChunkMultiple::can_append(DriveBitMultiple const &bit) const
{
  if (bit.multiple().size() != multiple_.size())
    return false;

  int const_drivers = 0;
  for (DriveChunk const &single : multiple_)
    if (single.is_constant())
      const_drivers += 1;

  if (const_drivers > 1)
    return false;

  for (DriveBit const &single : bit.multiple())
    if (single.is_constant())
      const_drivers -= 1;

  if (const_drivers != 0)
    return false;

  for (DriveChunk const &single : multiple_)
    {
      switch (single.type())
	{
	case DriveType::CONSTANT: {
	} break;
	case DriveType::WIRE: {
	  auto const &wire = single.wire();
	  DriveBit next = DriveBitWire(wire.wire, wire.offset + wire.width);
	  if (!bit.multiple().count(next))
	    return false;
	} break;
	case DriveType::PORT: {
	  auto const &port = single.port();
	  DriveBit next = DriveBitPort(port.cell, port.port, port.offset + port.width);
	  if (!bit.multiple().count(next))
	    return false;
	} break;
	case DriveType::MARKER: {
	  auto const &marker = single.marker();
	  DriveBit next = DriveBitMarker(marker.marker, marker.offset + marker.width);
	  if (!bit.multiple().count(next))
	    return false;
	} break;
	default:
	  return false;
	}
    }

  return true;
}

bool DriveChunkMultiple::can_append(DriveChunkMultiple const &chunk) const
{
  if (chunk.multiple().size() != multiple_.size())
    return false;

  int const_drivers = 0;
  for (DriveChunk const &single : multiple_)
    if (single.is_constant())
      const_drivers += 1;

  if (const_drivers > 1)
    return false;

  for (DriveChunk const &single : chunk.multiple())
    if (single.is_constant())
      const_drivers -= 1;

  if (const_drivers != 0)
    return false;

  for (DriveChunk const &single : multiple_)
    {
      switch (single.type())
	{
	case DriveType::CONSTANT: {
	} break;
	case DriveType::WIRE: {
	  auto const &wire = single.wire();
	  DriveChunk next = DriveChunkWire(wire.wire, wire.offset + wire.width, chunk.size());
	  if (!chunk.multiple().count(next))
	    return false;
	} break;
	case DriveType::PORT: {
	  auto const &port = single.port();
	  DriveChunk next = DriveChunkPort(port.cell, port.port, port.offset + port.width, chunk.size());
	  if (!chunk.multiple().count(next))
	    return false;
	} break;
	case DriveType::MARKER: {
	  auto const &marker = single.marker();
	  DriveChunk next = DriveChunkMarker(marker.marker, marker.offset + marker.width, chunk.size());
	  if (!chunk.multiple().count(next))
	    return false;
	} break;
	default:
	  return false;
	}
    }

  return true;
}

bool DriveChunkMultiple::try_append(DriveBitMultiple const &bit)
{
  if (!can_append(bit))
    return false;
  width_ += 1;
  State constant;

  for (DriveBit const &single : bit.multiple())
    if (single.is_constant())
      constant = single.constant();

  for (DriveChunk &single : multiple_)
    {
      switch (single.type())
	{
	case DriveType::CONSTANT: {
	  single.constant().bits.push_back(constant);
	} break;
	case DriveType::WIRE: {
	  single.wire().width += 1;
	} break;
	case DriveType::PORT: {
	  single.port().width += 1;
	} break;
	case DriveType::MARKER: {
	  single.marker().width += 1;
	} break;
	default:
	  log_abort();
	}
    }
  return true;
}

bool DriveChunkMultiple::try_append(DriveChunkMultiple const &chunk)
{
  if (!can_append(chunk))
    return false;
  int width = chunk.size();
  width_ += width;
  Const constant;

  for (DriveChunk const &single : chunk.multiple())
    if (single.is_constant())
      constant = single.constant();

  for (DriveChunk &single : multiple_)
    {
      switch (single.type())
	{
	case DriveType::CONSTANT: {
	  auto &bits = single.constant().bits;
	  bits.insert(bits.end(), constant.bits.begin(), constant.bits.end());
	} break;
	case DriveType::WIRE: {
	  single.wire().width += width;
	} break;
	case DriveType::PORT: {
	  single.port().width += width;
	} break;
	case DriveType::MARKER: {
	  single.marker().width += width;
	} break;
	default:
	  log_abort();
	}
    }
  return true;
}

DriveChunkMultiple::DriveChunkMultiple(DriveBitMultiple const &bit)
    : width_(1)
{
    for (auto const &bit : bit.multiple())
        multiple_.emplace(bit);
}

pool<DriveChunk> const &DriveChunkMultiple::multiple() const
{
    return multiple_;
}

int DriveChunkMultiple::size() const { return width_; }


bool DriveChunkMultiple::operator==(const DriveChunkMultiple &other) const
{
    return width_ == other.width_ && multiple_ == other.multiple_;
}

bool DriveChunkMultiple::operator<(const DriveChunkMultiple &other) const
{
    if (multiple_.size() < other.multiple_.size())
        multiple_.sort();
    return false; // TODO: implement, canonicalize order
}

unsigned int DriveChunkMultiple::hash() const
{
    return mkhash(width_, multiple_.hash());
}

bool DriveChunk::can_append(DriveBit const &bit) const
{
  if (size() == 0)
    return true;
  if (bit.type() != type_)
    return false;
  switch (type_)
    {
    case DriveType::NONE:
      return true;
    case DriveType::CONSTANT:
      return true;
    case DriveType::WIRE:
      return wire_.can_append(bit.wire());
    case DriveType::PORT:
      return port_.can_append(bit.port());
    case DriveType::MULTIPLE:
      return multiple_.can_append(bit.multiple());
    default:
      log_abort();
    }
}

bool DriveChunk::try_append(DriveBit const &bit)
{
  if (size() == 0)
    *this = bit;
  if (bit.type() != type_)
    return false;
  switch (type_)
    {
    case DriveType::NONE:
      none_ += 1;
      return true;
    case DriveType::CONSTANT:
      constant_.bits.push_back(bit.constant());
      return true;
    case DriveType::WIRE:
      return wire_.try_append(bit.wire());
    case DriveType::PORT:
      return port_.try_append(bit.port());
    case DriveType::MULTIPLE:
      return multiple_.try_append(bit.multiple());
    default:
      log_abort();
    }
}


bool DriveChunk::try_append(DriveChunk const &chunk)
{
  if (size() == 0)
    *this = chunk;
  if (chunk.type_ != type_)
    return false;
  switch (type_)
    {
    case DriveType::NONE:
      none_ += chunk.none_;
      return true;
    case DriveType::CONSTANT:
      constant_.bits.insert(constant_.bits.end(), chunk.constant_.bits.begin(), chunk.constant_.bits.end());
      return true;
    case DriveType::WIRE:
      return wire_.try_append(chunk.wire());
    case DriveType::PORT:
      return port_.try_append(chunk.port());
    case DriveType::MARKER:
      return marker_.try_append(chunk.marker());
    case DriveType::MULTIPLE:
      return multiple_.try_append(chunk.multiple());
    }
  log_abort();
}

DriveChunk::DriveChunk() { set_none(); }

DriveChunk::DriveChunk(DriveChunk const &other) { *this = other; }

DriveChunk::DriveChunk(DriveChunk &&other) { *this = std::move(other); }

DriveChunk::DriveChunk(DriveBit const &other) { *this = other; }

DriveChunk::DriveChunk(Const const &constant) { *this = constant; }

DriveChunk::DriveChunk(Const &&constant) { *this = std::move(constant); }

DriveChunk::DriveChunk(DriveChunkWire const &wire) { *this = wire; }

DriveChunk::DriveChunk(DriveChunkWire &&wire) { *this = std::move(wire); }

DriveChunk::DriveChunk(DriveChunkPort const &port) { *this = port; }

DriveChunk::DriveChunk(DriveChunkPort &&port) { *this = std::move(port); }

DriveChunk::DriveChunk(DriveChunkMarker const &marker) { *this = marker; }

DriveChunk::DriveChunk(DriveChunkMarker &&marker) { *this = std::move(marker); }

DriveChunk::DriveChunk(DriveChunkMultiple const &multiple) { *this = multiple; }

DriveChunk::DriveChunk(DriveChunkMultiple &&multiple) { *this = std::move(multiple); }

DriveChunk::~DriveChunk() { set_none(); }

DriveBit DriveChunk::operator[](int i) const
{
    switch (type_)
    {
    case DriveType::NONE:
        return DriveBit();
    case DriveType::CONSTANT:
        return constant_[i];
    case DriveType::WIRE:
        return wire_[i];
    case DriveType::PORT:
        return port_[i];
    case DriveType::MARKER:
        return marker_[i];
    case DriveType::MULTIPLE:
        return multiple_[i];
    }
    log_abort();
}

void DriveChunk::set_none(int width)
{
    switch (type_)
    {
    case DriveType::NONE:
        none_ = width;
        break;
    case DriveType::CONSTANT:
        constant_.~Const();
        break;
    case DriveType::WIRE:
        wire_.~DriveChunkWire();
        break;
    case DriveType::PORT:
        port_.~DriveChunkPort();
        break;
    case DriveType::MARKER:
        marker_.~DriveChunkMarker();
        break;
    case DriveType::MULTIPLE:
        multiple_.~DriveChunkMultiple();
        break;
    }
    type_ = DriveType::NONE;
    none_ = width;
}

DriveChunk &DriveChunk::operator=(DriveChunk const &other)
{
    switch (other.type_)
    {
    case DriveType::NONE:
        set_none(other.none_);
        break;
    case DriveType::CONSTANT:
        *this = other.constant_;
        break;
    case DriveType::WIRE:
        *this = other.wire_;
        break;
    case DriveType::PORT:
        *this = other.port_;
        break;
    case DriveType::MARKER:
        *this = other.marker_;
        break;
    case DriveType::MULTIPLE:
        *this = other.multiple_;
        break;
    }
    return *this;
}

DriveChunk &DriveChunk::operator=(DriveChunk &&other)
{
    switch (other.type_)
    {
    case DriveType::NONE:
        set_none(other.none_);
        break;
    case DriveType::CONSTANT:
        *this = std::move(other.constant_);
        break;
    case DriveType::WIRE:
        *this = std::move(other.wire_);
        break;
    case DriveType::PORT:
        *this = std::move(other.port_);
        break;
    case DriveType::MARKER:
        *this = std::move(other.marker_);
        break;
    case DriveType::MULTIPLE:
        *this = std::move(other.multiple_);
        break;
    }
    return *this;
}

DriveChunk &DriveChunk::operator=(Const const &constant)
{
    set_none();
    new (&constant_) Const(constant);
    type_ = DriveType::CONSTANT;
    return *this;
}

DriveChunk &DriveChunk::operator=(Const &&constant)
{
    set_none();
    new (&constant_) Const(std::move(constant));
    type_ = DriveType::CONSTANT;
    return *this;
}

DriveChunk &DriveChunk::operator=(DriveChunkWire const &wire)
{
    set_none();
    new (&wire_) DriveChunkWire(wire);
    type_ = DriveType::WIRE;
    return *this;
}

DriveChunk &DriveChunk::operator=(DriveChunkWire &&wire)
{
    set_none();
    new (&wire_) DriveChunkWire(std::move(wire));
    type_ = DriveType::WIRE;
    return *this;
}

DriveChunk &DriveChunk::operator=(DriveChunkPort const &port)
{
    set_none();
    new (&port_) DriveChunkPort(port);
    type_ = DriveType::PORT;
    return *this;
}

DriveChunk &DriveChunk::operator=(DriveChunkPort &&port)
{
    set_none();
    new (&port_) DriveChunkPort(std::move(port));
    type_ = DriveType::PORT;
    return *this;
}

DriveChunk &DriveChunk::operator=(DriveChunkMarker const &marker)
{
    set_none();
    new (&marker_) DriveChunkMarker(marker);
    type_ = DriveType::MARKER;
    return *this;
}

DriveChunk &DriveChunk::operator=(DriveChunkMarker &&marker)
{
    set_none();
    new (&marker_) DriveChunkMarker(std::move(marker));
    type_ = DriveType::MARKER;
    return *this;
}

DriveChunk &DriveChunk::operator=(DriveChunkMultiple const &multiple)
{
    set_none(multiple.size());
    if (multiple.multiple().empty())
        return *this;
    new (&multiple_) DriveChunkMultiple(multiple);
    type_ = DriveType::MULTIPLE;
    return *this;
}

DriveChunk &DriveChunk::operator=(DriveChunkMultiple &&multiple)
{
    set_none(multiple.size());
    if (multiple.multiple().empty())
        return *this;
    new (&multiple_) DriveChunkMultiple(std::move(multiple));
    type_ = DriveType::MULTIPLE;
    return *this;
}

DriveChunk &DriveChunk::operator=(DriveBit const &other)
{
    switch (other.type())
    {
    case DriveType::NONE:
        set_none(1);
        break;
    case DriveType::CONSTANT:
        *this = Const(other.constant());
        break;
    case DriveType::WIRE:
        *this = DriveChunkWire(other.wire());
        break;
    case DriveType::PORT:
        *this = DriveChunkPort(other.port());
        break;
    case DriveType::MARKER:
        *this = DriveChunkMarker(other.marker());
        break;
    case DriveType::MULTIPLE:
        *this = DriveChunkMultiple(other.multiple());
        break;
    }
    return *this;
}

unsigned int DriveChunk::hash() const
{
    unsigned int inner;
    switch (type_)
    {
    case DriveType::NONE:
        inner = 0;
        break;
    case DriveType::CONSTANT:
        inner = constant_.hash();
        break;
    case DriveType::WIRE:
        inner = wire_.hash();
        break;
    case DriveType::PORT:
        inner = port_.hash();
        break;
    case DriveType::MARKER:
        inner = marker_.hash();
        break;
    case DriveType::MULTIPLE:
        inner = multiple_.hash();
        break;
    }
    return mkhash((unsigned int)type_, inner);
}

bool DriveChunk::operator==(const DriveChunk &other) const
{
    if (type_ != other.type_)
        return false;

    switch (type_)
    {
    case DriveType::NONE:
        return true;
    case DriveType::CONSTANT:
        return constant_ == other.constant_;
    case DriveType::WIRE:
        return wire_ == other.wire_;
    case DriveType::PORT:
        return port_ == other.port_;
    case DriveType::MARKER:
        return marker_ == other.marker_;
    case DriveType::MULTIPLE:
        return multiple_ == other.multiple_;
    }
    log_assert(false);
}

bool DriveChunk::operator!=(const DriveChunk &other) const
{
    return !(*this == other);
}

bool DriveChunk::operator<(const DriveChunk &other) const
{
    if (type_ != other.type_)
        return type_ < other.type_;
    switch (type_)
    {
    case DriveType::NONE:
        return false;
    case DriveType::CONSTANT:
        return constant_ < other.constant_;
    case DriveType::WIRE:
        return wire_ < other.wire_;
    case DriveType::PORT:
        return port_ < other.port_;
    case DriveType::MARKER:
        return marker_ < other.marker_;
    case DriveType::MULTIPLE:
        return multiple_ < other.multiple_;
    }
    log_assert(false);
}

DriveType DriveChunk::type() const { return type_; }

bool DriveChunk::is_none() const { return type_ == DriveType::NONE; }

bool DriveChunk::is_constant() const { return type_ == DriveType::CONSTANT; }

bool DriveChunk::is_wire() const { return type_ == DriveType::WIRE; }

bool DriveChunk::is_port() const { return type_ == DriveType::PORT; }

bool DriveChunk::is_marker() const { return type_ == DriveType::MARKER; }

bool DriveChunk::is_multiple() const { return type_ == DriveType::MULTIPLE; }

Const &DriveChunk::constant()
{
    log_assert(is_constant());
    return constant_;
}

Const const &DriveChunk::constant() const
{
    log_assert(is_constant());
    return constant_;
}

DriveChunkWire &DriveChunk::wire()
{
    log_assert(is_wire());
    return wire_;
}

DriveChunkWire const &DriveChunk::wire() const
{
    log_assert(is_wire());
    return wire_;
}

DriveChunkPort &DriveChunk::port()
{
    log_assert(is_port());
    return port_;
}

DriveChunkPort const &DriveChunk::port() const
{
    log_assert(is_port());
    return port_;
}

DriveChunkMarker &DriveChunk::marker()
{
    log_assert(is_marker());
    return marker_;
}

DriveChunkMarker const &DriveChunk::marker() const
{
    log_assert(is_marker());
    return marker_;
}

DriveChunkMultiple &DriveChunk::multiple()
{
    log_assert(is_multiple());
    return multiple_;
}

DriveChunkMultiple const &DriveChunk::multiple() const
{
    log_assert(is_multiple());
    return multiple_;
}

int DriveChunk::size() const
{
    switch (type_)
    {
    case DriveType::NONE:
        return none_;
    case DriveType::CONSTANT:
        return constant_.size();
    case DriveType::WIRE:
        return wire_.size();
    case DriveType::PORT:
        return port_.size();
    case DriveType::MARKER:
        return marker_.size();
    case DriveType::MULTIPLE:
        return multiple_.size();
    default:
        log_assert(false && "unsupported type");
    }
}

void DriveSpec::append(DriveBit const &bit)
{
  hash_ = 0;
  if (!packed()) {
    bits_.push_back(bit);
    width_ += 1;
    return;
  }

  if (chunks_.empty() || !chunks_.back().try_append(bit))
    chunks_.emplace_back(bit);
  width_ += 1;
}

void DriveSpec::append(DriveChunk const &chunk)
{
  hash_ = 0;
  pack();
  if (chunks_.empty() || !chunks_.back().try_append(chunk))
    chunks_.emplace_back(chunk);
  width_ += chunk.size();
}

void DriveSpec::pack() const {
  if (bits_.empty())
    return;
  std::vector<DriveBit> bits(std::move(bits_));
  for (auto &bit : bits)
    if (chunks_.empty() || !chunks_.back().try_append(bit))
      chunks_.emplace_back(std::move(bit));
}

void DriveSpec::unpack() const {
  if (chunks_.empty())
    return;
  for (auto &chunk : chunks_)
    {
      for (int i = 0, width = chunk.size(); i != width; ++i)
	{
	  bits_.emplace_back(chunk[i]);
	}
    }
  chunks_.clear();
}

void DriveSpec::compute_width()
{
  width_ = 0;
  for (auto const &chunk : chunks_)
    width_ += chunk.size();
}


inline bool DriveSpec::packed() const
{
    return bits_.empty();
}

DriveSpec::DriveSpec() {}

DriveSpec::DriveSpec(DriveChunk const &chunk)
{
    *this = chunk;
}

DriveSpec::DriveSpec(DriveChunkWire const &chunk)
{
    *this = chunk;
}

DriveSpec::DriveSpec(DriveChunkPort const &chunk)
{
    *this = chunk;
}

DriveSpec::DriveSpec(DriveChunkMarker const &chunk)
{
    *this = chunk;
}

DriveSpec::DriveSpec(DriveChunkMultiple const &chunk)
{
    *this = chunk;
}

DriveSpec::DriveSpec(DriveBit const &bit)
{
    *this = bit;
}

DriveSpec::DriveSpec(DriveBitWire const &bit)
{
    *this = bit;
}

DriveSpec::DriveSpec(DriveBitPort const &bit)
{
    *this = bit;
}

DriveSpec::DriveSpec(DriveBitMarker const &bit)
{
    *this = bit;
}

DriveSpec::DriveSpec(DriveBitMultiple const &bit)
{
    *this = bit;
}

DriveSpec::DriveSpec(std::vector<DriveChunk> const &chunks) : chunks_(chunks)
{
    compute_width();
}

DriveSpec::DriveSpec(std::vector<DriveBit> const &bits)
{
    for (auto const &bit : bits)
        append(bit);
}

std::vector<DriveChunk> const &DriveSpec::chunks() const
{
    pack();
    return chunks_;
}

std::vector<DriveBit> const &DriveSpec::bits() const
{
    unpack();
    return bits_;
}

int DriveSpec::size() const
{
    return width_;
}

DriveBit &DriveSpec::operator[](int index)
{
    log_assert(index >= 0 && index < size());
    unpack();
    return bits_[index];
}

const DriveBit &DriveSpec::operator[](int index) const
{
    log_assert(index >= 0 && index < size());
    unpack();
    return bits_[index];
}

void DriveSpec::clear()
{
    chunks_.clear();
    bits_.clear();
    width_ = 0;
}

DriveSpec &DriveSpec::operator=(DriveChunk const &chunk)
{
    chunks_.clear();
    bits_.clear();
    append(chunk);
    return *this;
}

DriveSpec &DriveSpec::operator=(DriveChunkWire const &chunk)
{
    return *this = DriveChunk(chunk);
}

DriveSpec &DriveSpec::operator=(DriveChunkPort const &chunk)
{
    return *this = DriveChunk(chunk);
}

DriveSpec &DriveSpec::operator=(DriveChunkMarker const &chunk)
{
    return *this = DriveChunk(chunk);
}

DriveSpec &DriveSpec::operator=(DriveChunkMultiple const &chunk)
{
    return *this = DriveChunk(chunk);
}

DriveSpec &DriveSpec::operator=(DriveBit const &bit)
{
    chunks_.clear();
    bits_.clear();
    append(bit);
    return *this;
}

DriveSpec &DriveSpec::operator=(DriveBitWire const &bit)
{
    return *this = DriveBit(bit);
}

DriveSpec &DriveSpec::operator=(DriveBitPort const &bit)
{
    return *this = DriveBit(bit);
}

DriveSpec &DriveSpec::operator=(DriveBitMarker const &bit)
{
    return *this = DriveBit(bit);
}

DriveSpec &DriveSpec::operator=(DriveBitMultiple const &bit)
{
    return *this = DriveBit(bit);
}

unsigned int DriveSpec::hash() const
{
    if (hash_ != 0)
        return hash_;

    pack();
    hash_ = hash_ops<std::vector<DriveChunk>>().hash(chunks_);
    hash_ |= (hash_ == 0);
    return hash_;
}

bool DriveSpec::operator==(DriveSpec const &other) const
{
    if (size() != other.size() || hash() != other.hash())
        return false;
    return chunks() == other.chunks();
}

void DriverMap::DriveBitGraph::add_edge(DriveBitId src, DriveBitId dst)
{
  if (first_edges.emplace(src, dst).first->second == dst)
    return;
  if (second_edges.emplace(src, dst).first->second == dst)
    return;
  more_edges[src].emplace(dst);
}

DriverMap::DriveBitId DriverMap::DriveBitGraph::pop_edge(DriveBitId src)
{
  // TODO unused I think?
  auto found_more = more_edges.find(src);
  if (found_more != more_edges.end()) {
    auto result = found_more->second.pop();
    if (found_more->second.empty())
      more_edges.erase(found_more);
    return result;
  }

  auto found_second = second_edges.find(src);
  if (found_second != second_edges.end()) {
    auto result = found_second->second;
    second_edges.erase(found_second);
    return result;
  }

  auto found_first = first_edges.find(src);
  if (found_first != first_edges.end()) {
    auto result = found_first->second;
    first_edges.erase(found_first);
    return result;
  }

  return DriveBitId();
}

void DriverMap::DriveBitGraph::clear(DriveBitId src)
{
  first_edges.erase(src);
  second_edges.erase(src);
  more_edges.erase(src);
}

bool DriverMap::DriveBitGraph::contains(DriveBitId src)
{
  return first_edges.count(src);
}

int DriverMap::DriveBitGraph::count(DriveBitId src)
{
  if (!first_edges.count(src))
    return 0;
  if (!second_edges.count(src))
    return 1;
  auto found = more_edges.find(src);
  if (found == more_edges.end())
    return 2;
  return GetSize(found->second) + 2;
}

DriverMap::DriveBitId DriverMap::DriveBitGraph::at(DriveBitId src, int index)
{
  if (index == 0)
    return first_edges.at(src);
  else if (index == 1)
    return second_edges.at(src);
  else
    return *more_edges.at(src).element(index - 2);
}


DriverMap::BitMode DriverMap::bit_mode(DriveBit const &bit)
{
  switch (bit.type())
    {
    case DriveType::NONE:
      return BitMode::NONE;
    case DriveType::CONSTANT:
      // TODO how to handle Sx here?
      return bit.constant() == State::Sz ? BitMode::NONE : BitMode::DRIVER;
    case DriveType::WIRE: {
      auto const &wire = bit.wire();
      bool driver = wire.wire->port_input;
      bool driven = wire.wire->port_output;

      if (driver && !driven)
	return BitMode::DRIVER;
      else if (driven && !driver)
	return BitMode::DRIVEN;
      else if (driver && driven)
	return BitMode::TRISTATE;
      else
	return keep_wire(bit.wire().wire) ? BitMode::KEEP : BitMode::NONE;
    }
    case DriveType::PORT: {
      auto const &port = bit.port();
      bool driver = celltypes.cell_output(port.cell->type, port.port);
      bool driven = celltypes.cell_input(port.cell->type, port.port);
      if (driver && !driven)
	return BitMode::DRIVER;
      else if (driven && !driver)
	return BitMode::DRIVEN_UNIQUE;
      else
	return BitMode::TRISTATE;
    }
    case DriveType::MARKER: {
      // TODO user supplied classification
      log_abort();
    }
    default:
      log_abort();
    }
}

DriverMap::DriveBitId DriverMap::id_from_drive_bit(DriveBit const &bit)
{
  switch (bit.type())
    {
    case DriveType::NONE:
      return -1;
    case DriveType::CONSTANT:
      return (int)bit.constant();
    case DriveType::WIRE: {
      auto const &wire_bit = bit.wire();
      int offset = next_offset;
      auto insertion = wire_offsets.emplace(wire_bit.wire, offset);
      if (insertion.second) {
	if (wire_bit.wire->width == 1) {
	  log_assert(wire_bit.offset == 0);
	  isolated_drive_bits.emplace(offset, bit);
	} else
	  drive_bits.emplace(offset, DriveBitWire(wire_bit.wire, 0));
	next_offset += wire_bit.wire->width;
      }
      return insertion.first->second.id + wire_bit.offset;
    }
    case DriveType::PORT: {
      auto const &port_bit = bit.port();
      auto key = std::make_pair(port_bit.cell, port_bit.port);
      int offset = next_offset;
      auto insertion = port_offsets.emplace(key, offset);
      if (insertion.second) {
	int width = port_bit.cell->connections().at(port_bit.port).size();
	if (width == 1 && offset == 0) {
	  log_assert(port_bit.offset == 0);
	  isolated_drive_bits.emplace(offset, bit);
	} else
	  drive_bits.emplace(offset, DriveBitPort(port_bit.cell, port_bit.port, 0));
	next_offset += width;
      }
      return insertion.first->second.id + port_bit.offset;
    }
    default:
      log_assert(false && "unsupported DriveType in DriverMap");
    }
  log_abort();
}

DriveBit DriverMap::drive_bit_from_id(DriveBitId id)
{
  auto found_isolated = isolated_drive_bits.find(id);
  if (found_isolated != isolated_drive_bits.end())
    return found_isolated->second;

  auto found = drive_bits.upper_bound(id);
  if (found == drive_bits.begin()) {
    return id < 0 ? DriveBit() : DriveBit((State) id.id);
  }
  --found;
  DriveBit result = found->second;
  if (result.is_wire()) {
    result.wire().offset += id.id - found->first.id;
  } else {
    log_assert(result.is_port());
    result.port().offset += id.id - found->first.id;
  }
  return result;
}

void DriverMap::connect_directed_merge(DriveBitId driven_id, DriveBitId driver_id)
{
  if (driven_id == driver_id)
    return;

  same_driver.merge(driven_id, driver_id);

  for (int i = 0, end = connected_drivers.count(driven_id); i != end; ++i)
    connected_drivers.add_edge(driver_id, connected_drivers.at(driven_id, i));

  connected_drivers.clear(driven_id);

  for (int i = 0, end = connected_undirected.count(driven_id); i != end; ++i)
    connected_undirected.add_edge(driver_id, connected_undirected.at(driven_id, i));

  connected_undirected.clear(driven_id);
}

void DriverMap::connect_directed_buffer(DriveBitId driven_id, DriveBitId driver_id)
{
  connected_drivers.add_edge(driven_id, driver_id);
}

void DriverMap::connect_undirected(DriveBitId a_id, DriveBitId b_id)
{
  connected_undirected.add_edge(a_id, b_id);
  connected_undirected.add_edge(b_id, a_id);
}

void DriverMap::add(Module *module)
{
  for (auto const &conn : module->connections())
    add(conn.first, conn.second);

  for (auto cell : module->cells())
    for (auto const &conn : cell->connections())
      add_port(cell, conn.first, conn.second);
}

// Add a single bit connection to the driver map.
void DriverMap::add(DriveBit const &a, DriveBit const &b)
{
  DriveBitId a_id = id_from_drive_bit(a);
  DriveBitId b_id = id_from_drive_bit(b);

  DriveBitId orig_a_id = a_id;
  DriveBitId orig_b_id = b_id;

  a_id = same_driver.find(a_id);
  b_id = same_driver.find(b_id);

  if (a_id == b_id)
    return;

  BitMode a_mode = bit_mode(orig_a_id == a_id ? a : drive_bit_from_id(a_id));
  BitMode b_mode = bit_mode(orig_b_id == b_id ? b : drive_bit_from_id(b_id));

  // If either bit is just a wire that we don't need to keep, merge and
  // use the other end as representative bit.
  if (a_mode == BitMode::NONE && !(b_mode == BitMode::DRIVEN_UNIQUE || b_mode == BitMode::DRIVEN))
    connect_directed_merge(a_id, b_id);
  else if (b_mode == BitMode::NONE && !(a_mode == BitMode::DRIVEN_UNIQUE || a_mode == BitMode::DRIVEN))
    connect_directed_merge(b_id, a_id);
  // If either bit requires a driven value and has a unique driver, merge
  // and use the other end as representative bit.
  else if (a_mode == BitMode::DRIVEN_UNIQUE && !(b_mode == BitMode::DRIVEN_UNIQUE || b_mode == BitMode::DRIVEN))
    connect_directed_buffer(a_id, b_id);
  else if (b_mode == BitMode::DRIVEN_UNIQUE && !(a_mode == BitMode::DRIVEN_UNIQUE || a_mode == BitMode::DRIVEN))
    connect_directed_buffer(b_id, a_id);
  // If either bit only drives a value, store a directed connection from
  // it to the other bit.
  else if (a_mode == BitMode::DRIVER)
    connect_directed_buffer(b_id, a_id);
  else if (b_mode == BitMode::DRIVER)
    connect_directed_buffer(a_id, b_id);
  // Otherwise we store an undirected connection which we will resolve
  // during querying.
  else
    connect_undirected(a_id, b_id);

  return;
}

// Specialized version that avoids unpacking
void DriverMap::add(SigSpec const &a, SigSpec const &b)
{
  log_assert(a.size() == b.size());
  auto const &a_chunks = a.chunks();
  auto const &b_chunks = b.chunks();

  auto a_chunk = a_chunks.begin();
  auto a_end = a_chunks.end();
  int a_offset = 0;

  auto b_chunk = b_chunks.begin();
  int b_offset = 0;

  SigChunk tmp_a, tmp_b;
  while (a_chunk != a_end) {
    int a_width = a_chunk->width - a_offset;
    if (a_width == 0) {
      a_offset = 0;
      ++a_chunk;
      continue;
    }
    int b_width = b_chunk->width - b_offset;
    if (b_width == 0) {
      b_offset = 0;
      ++b_chunk;
      continue;
    }
    int width = std::min(a_width, b_width);
    log_assert(width > 0);

    SigChunk const &a_subchunk =
      a_offset == 0 && a_width == width ? *a_chunk : a_chunk->extract(a_offset, width);
    SigChunk const &b_subchunk =
      b_offset == 0 && b_width == width ? *b_chunk : b_chunk->extract(b_offset, width);

    add(a_subchunk, b_subchunk);

    a_offset += width;
    b_offset += width;
  }
}

void DriverMap::add_port(Cell *cell, IdString const &port, SigSpec const &b)
{
  int offset = 0;
  for (auto const &chunk : b.chunks()) {
    add(chunk, DriveChunkPort(cell, port, offset, chunk.width));
    offset += chunk.size();
  }
}

void DriverMap::orient_undirected(DriveBitId id)
{
  pool<DriveBitId> &seen = orient_undirected_seen;
  pool<DriveBitId> &drivers = orient_undirected_drivers;
  dict<DriveBitId, int> &distance = orient_undirected_distance;
  seen.clear();
  drivers.clear();

  seen.emplace(id);

  for (int pos = 0; pos < GetSize(seen); ++pos) {
    DriveBitId current = *seen.element(seen.size() - 1 - pos);
    DriveBit bit = drive_bit_from_id(current);

    BitMode mode = bit_mode(bit);

    if (mode == BitMode::DRIVER || mode == BitMode::TRISTATE)
      drivers.emplace(current);

    if (connected_drivers.contains(current))
      drivers.emplace(current);

    int undirected_driver_count = connected_undirected.count(current);

    for (int i = 0; i != undirected_driver_count; ++i)
      seen.emplace(same_driver.find(connected_undirected.at(current, i)));
  }

  if (drivers.empty())
    for (auto seen_id : seen)
      drivers.emplace(seen_id);

  for (auto driver : drivers)
    {
      distance.clear();
      distance.emplace(driver, 0);

      for (int pos = 0; pos < GetSize(distance); ++pos) {
	auto current_it = distance.element(distance.size() - 1 - pos);

	DriveBitId current = current_it->first;
	int undirected_driver_count = connected_undirected.count(current);

	for (int i = 0; i != undirected_driver_count; ++i)
	  {
	    DriveBitId next = same_driver.find(connected_undirected.at(current, i));
	    auto emplaced = distance.emplace(next, current_it->second + 1);
	    if (emplaced.first->second == current_it->second + 1)
	      connected_oriented.add_edge(next, current);
	  }
      }
    }

  for (auto seen_id : seen)
    oriented_present.emplace(seen_id);
}

DriveBit DriverMap::operator()(DriveBit const &bit)
{
  if (bit.type() == DriveType::MARKER || bit.type() == DriveType::NONE)
    return bit;
  if (bit.type() == DriveType::MULTIPLE)
    {
      DriveBit result;
      for (auto const &inner : bit.multiple().multiple())
	result.merge((*this)(inner));
      return result;
    }

  DriveBitId bit_id = id_from_drive_bit(bit);

  DriveBitId bit_repr_id = same_driver.find(bit_id);

  DriveBit bit_repr = drive_bit_from_id(bit_repr_id);

  BitMode mode = bit_mode(bit_repr);

  if (mode == BitMode::KEEP && bit_repr_id != bit_id)
    return bit_repr;

  int implicit_driver_count = connected_drivers.count(bit_repr_id);
  if (connected_undirected.contains(bit_repr_id) && !oriented_present.count(bit_repr_id))
    orient_undirected(bit_repr_id);

  DriveBit driver;

  if (mode == BitMode::DRIVER || mode == BitMode::TRISTATE)
    driver = bit_repr;

  for (int i = 0; i != implicit_driver_count; ++i)
    driver.merge(drive_bit_from_id(connected_drivers.at(bit_repr_id, i)));

  int oriented_driver_count = connected_oriented.count(bit_repr_id);
  for (int i = 0; i != oriented_driver_count; ++i)
    driver.merge(drive_bit_from_id(connected_oriented.at(bit_repr_id, i)));

  return driver;
}

DriveSpec DriverMap::operator()(DriveSpec spec)
{
  DriveSpec result;

  for (int i = 0, width = spec.size(); i != width; ++i)
    result.append((*this)(spec[i]));

  return result;
}

const char *log_signal(DriveChunkWire const &chunk)
{
  const char *id = log_id(chunk.wire->name);
  if (chunk.is_whole())
    return id;
  if (chunk.width == 1)
    return log_str(stringf("%s [%d]", id, chunk.offset));
  return log_str(stringf("%s [%d:%d]", id, chunk.offset + chunk.width - 1, chunk.offset));
}


const char *log_signal(DriveChunkPort const &chunk)
{
  const char *cell_id = log_id(chunk.cell->name);
  const char *port_id = log_id(chunk.port);
  if (chunk.is_whole())
    return log_str(stringf("%s <%s>", cell_id, port_id));
  if (chunk.width == 1)
    return log_str(stringf("%s <%s> [%d]", cell_id, port_id, chunk.offset));
  return log_str(stringf("%s <%s> [%d:%d]", cell_id, port_id, chunk.offset + chunk.width - 1, chunk.offset));
}

const char *log_signal(DriveChunkMarker const &chunk)
{
  if (chunk.width == 1)
    return log_str(stringf("<marker %d> [%d]", chunk.marker, chunk.offset));
  return log_str(stringf("<marker %d> [%d:%d]", chunk.marker, chunk.offset + chunk.width - 1, chunk.offset));
}

const char *log_signal(DriveChunk const &chunk)
{
  switch (chunk.type())
    {
    case DriveType::NONE:
      return log_str(stringf("<none x%d>", chunk.size()));
    case DriveType::CONSTANT:
      return log_const(chunk.constant());
    case DriveType::WIRE:
      return log_signal(chunk.wire());
    case DriveType::PORT:
      return log_signal(chunk.port());
    case DriveType::MARKER:
      return log_signal(chunk.marker());
    case DriveType::MULTIPLE: {
      std::string str = "<multiple";
      const char *sep = " ";
      for (auto const &single : chunk.multiple().multiple()) {
	str += sep;
	sep = ", ";
	str += log_signal(single);
      }
      str += ">";
      return log_str(str);
    }
    default:
      log_abort();
    }
}

const char *log_signal(DriveSpec const &spec)
{
  auto &chunks = spec.chunks();
  if (chunks.empty())
    return "{}";
  if (chunks.size() == 1)
    return log_signal(chunks[0]);

  std::string str;
  const char *sep = "{ ";

  for (auto i = chunks.rbegin(), end = chunks.rend(); i != end; ++i)
    {
      str += sep;
      sep = " ";
      str += log_signal(*i);
    }
  str += " }";

  return log_str(str);
}

DriverMap::DriverMap() : next_offset(1 + static_cast<int>(State::Sm))
{
    celltypes.setup();
}

DriverMap::DriverMap(Design *design) : next_offset(1 + static_cast<int>(State::Sm))
{
    celltypes.setup();
    celltypes.setup_design(design);
}

DriverMap::DriveBitId::DriveBitId() : id(-1) {}

DriverMap::DriveBitId::DriveBitId(int id) : id(id) {}

bool DriverMap::DriveBitId::operator==(const DriveBitId &other) const
{
    return id == other.id;
}

bool DriverMap::DriveBitId::operator!=(const DriveBitId &other) const
{
    return id != other.id;
}

bool DriverMap::DriveBitId::operator<(const DriveBitId &other) const
{
    return id < other.id;
}

unsigned int DriverMap::DriveBitId::hash() const
{
    return id;
}

bool DriverMap::keep_wire(Wire *wire) {
  // TODO configurable
  return wire->has_attribute(ID(keep));
}


YOSYS_NAMESPACE_END
