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


void DriveBitMultiple::merge(DriveBit const &single)
{
	if (single.type() == DriveType::NONE)
		return;
	if (single.type() == DriveType::MULTIPLE) {
		merge(single.multiple());
		return;
	}
	multiple_.emplace(single);
}

void DriveBitMultiple::merge(DriveBit &&single)
{
	if (single.type() == DriveType::NONE)
		return;
	if (single.type() == DriveType::MULTIPLE) {
		merge(std::move(single.multiple()));
		return;
	}
	multiple_.emplace(std::move(single));
}

DriveBitMultiple DriveChunkMultiple::operator[](int i) const
{
	DriveBitMultiple result;
	for (auto const &single : multiple_)
		result.merge(single[i]);
	return result;
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
				single.constant().bits().push_back(constant);
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
				auto &bits = single.constant().bits();
				bits.insert(bits.end(), constant.bits().begin(), constant.bits().end());
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
			constant_.bits().push_back(bit.constant());
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
			constant_.bits().insert(constant_.bits().end(), chunk.constant_.begin(), chunk.constant_.end());
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

YOSYS_NAMESPACE_END
