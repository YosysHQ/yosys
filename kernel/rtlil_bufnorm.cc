/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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

#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/modtools.h"

#include <string.h>
#include <algorithm>
#include <optional>

YOSYS_NAMESPACE_BEGIN


void RTLIL::Design::bufNormalize(bool enable)
{
	if (!enable)
	{
		if (!flagBufferedNormalized)
			return;

		for (auto module : modules()) {
			module->buf_norm_cell_queue.clear();
			module->buf_norm_wire_queue.clear();
			module->buf_norm_cell_port_queue.clear();
			for (auto wire : module->wires()) {
				wire->driverCell_ = nullptr;
				wire->driverPort_ = IdString();
			}
			module->buf_norm_connect_index.clear();
		}

		flagBufferedNormalized = false;
		return;
	}

	if (!flagBufferedNormalized)
	{
		for (auto module : modules())
		{
			// When entering buf normalized mode, we need the first module-level bufNormalize
			// call to know about all drivers, about all module ports (whether represented by
			// a cell or not) and about all used but undriven wires (whether represented by a
			// cell or not). We ensure this by enqueing all cell output ports and all wires.

			for (auto cell : module->cells())
			for (auto &conn : cell->connections()) {
				if (GetSize(conn.second) == 0 || (cell->port_dir(conn.first) != RTLIL::PD_OUTPUT && cell->port_dir(conn.first) != RTLIL::PD_INOUT))
					continue;
				module->buf_norm_cell_queue.insert(cell);
				module->buf_norm_cell_port_queue.emplace(cell, conn.first);
			}
			for (auto wire : module->wires())
				module->buf_norm_wire_queue.insert(wire);

		}

		flagBufferedNormalized = true;
	}

	for (auto module : modules())
		module->bufNormalize();
}

struct bit_drive_data_t {
	int drivers = 0;
	int inout = 0;
	int users = 0;
};

typedef ModWalker::PortBit PortBit;

void RTLIL::Module::bufNormalize()
{
	// Since this is kernel code, we only log with yosys_xtrace set to not get
	// in the way when using `debug` to debug specific passes.q
#define xlog(...) do { if (yosys_xtrace) log("#X [bufnorm] " __VA_ARGS__); } while (0)

	if (!design->flagBufferedNormalized)
		return;

	if (!buf_norm_cell_queue.empty() || !buf_norm_wire_queue.empty() || !connections_.empty())
	{
		// Ensure that every enqueued input port is represented by a cell
		for (auto wire : buf_norm_wire_queue) {
			if (wire->port_input && !wire->port_output) {
				if (wire->driverCell_ != nullptr && wire->driverCell_->type != ID($input_port)) {
					wire->driverCell_ = nullptr;
					wire->driverPort_.clear();
				}
				if (wire->driverCell_ == nullptr) {
					Cell *input_port_cell = addCell(NEW_ID, ID($input_port));
					input_port_cell->setParam(ID::WIDTH, GetSize(wire));
					input_port_cell->setPort(ID::Y, wire); // this hits the fast path that doesn't mutate the queues
				}
			}
		}

		// Next we will temporarily undo buf normalization locally for
		// everything enqueued. This means we will turn $buf and $connect back
		// into connections. When doing this we also need to enqueue the other
		// end of $buf and $connect cells, so we use a queue and do this until
		// reaching a fixed point.

		// While doing this, we will also discover all drivers fully connected
		// to enqueued wires. We keep track of which wires are driven by a
		// unique and full cell ports (in which case the wire can stay
		// connected to the port) and which cell ports will need to be
		// reconnected to a fresh intermediate wire to re-normalize the module.

		idict<Wire *> wire_queue_entries; // Ordered queue of wires to process
		int wire_queue_pos = 0; // Index up to which we processed the wires

		// Wires with their unique driving cell port. We pick the first driver
		// we encounter, with the exception that we ensure that a module input
		// port can only get $input_port drivers and that $input_port drivers
		// cannot drive any other modules. If we reject an $input_port driver
		// because it's not driving an input port or because there already is
		// another $input_port driver for the same port, we also delete that
		// $input_port cell.
		dict<Wire *, std::pair<Cell *, IdString>> direct_driven_wires;

		// Set of cell ports that need a fresh intermediate wire. These are all
		// cell ports that drive non-full-wire sigspecs, cell ports driving
		// module input ports, and cell ports driving wires that are already
		// driven.
		pool<std::pair<Cell *, IdString>> pending_ports;

		// This helper will be called for every output/inout cell port that is
		// already enqueued or becomes reachable when denormalizing $buf or
		// $connect cells.
		auto enqueue_cell_port = [&](Cell *cell, IdString port) {
			xlog("processing cell port %s.%s\n", log_id(cell), log_id(port));

			// An empty cell type means the cell got removed
			if (cell->type.empty())
				return;


			SigSpec const &sig = cell->getPort(port);

			// Make sure all wires of the cell port are enqueued, ensuring we
			// detect other connected drivers (output and inout).
			for (auto chunk : sig.chunks())
				if (chunk.is_wire())
					wire_queue_entries(chunk.wire);

			if (cell->type == ID($buf) && cell->attributes.empty() && !cell->name.isPublic()) {
				// For a plain `$buf` cell, we enqueue all wires on its input
				// side, bypass it using module level connections (skipping 'z
				// bits) and then remove the cell. Eventually the module level
				// connections will turn back into `$buf` and `$connect` cells,
				// but since we also need to handle externally added module
				// level connections, turning everything into connections first
				// simplifies the logic for doing so.

				// TODO: We could defer removing the $buf cells here, and
				// re-use them in case we would create a new identical cell
				// later.
				log_assert(port == ID::Y);
				SigSpec sig_a = cell->getPort(ID::A);
				SigSpec sig_y = sig;

				for (auto const &s : {sig_a, sig})
					for (auto const &chunk : s.chunks())
						if (chunk.wire)
							wire_queue_entries(chunk.wire);

				if (sig_a.has_const(State::Sz)) {
					SigSpec new_a;
					SigSpec new_y;
					for (int i = 0; i < GetSize(sig_a); ++i) {
						SigBit b = sig_a[i];
						if (b == State::Sz)
							continue;
						new_a.append(b);
						new_y.append(sig_y[i]);
					}
					sig_a = std::move(new_a);
					sig_y = std::move(new_y);
				}

				if (!sig_y.empty())
					connect(sig_y, sig_a);
				remove(cell);
				log_assert(GetSize(buf_norm_wire_queue) <= 1);
				buf_norm_wire_queue.clear();
				return;
			} else if (cell->type == ID($input_port)) {
				log_assert(port == ID::Y);
				if (sig.is_wire()) {
					Wire *w = sig.as_wire();
					if (w->port_input && !w->port_output) {
						// An $input_port cell can only drive a full wire module input port
						auto [found, inserted] = direct_driven_wires.emplace(w, {cell, port});
						if (!inserted || (found->second.first == cell && found->second.second == port))
							return;
					}
				}

				// If an `$input_port` cell isn't driving a full
				// input port wire, we remove it since the wires are still the
				// canonical source of module ports

				buf_norm_cell_queue.insert(cell);
				remove(cell);
				log_assert(GetSize(buf_norm_wire_queue) <= 1);
				buf_norm_wire_queue.clear();
				return;
			}

			if (sig.is_wire()) {
				Wire *w = sig.as_wire();
				if (!w->port_input || w->port_output) {
					// If the full cell port is connected to a full non-input-port wire, pick it as driver
					auto [found, inserted] = direct_driven_wires.emplace(w, {cell, port});
					if (inserted || (found->second.first == cell && found->second.second == port))
						return;
				}
			}

			// Adds this port to the ports that need a fresh intermediate wire.
			// For full wires uniquely driven by a full output port, this isn't
			// reached due to the `return` above.
			pending_ports.emplace(cell, port);
		};

		// We enqueue all enqueued wires for `$buf`/`$connect` processing (clearing the module level queue).
		for (auto wire : buf_norm_wire_queue)
			wire_queue_entries(wire);
		buf_norm_wire_queue.clear();

		// Only after clearing the `buf_norm_wire_queue` are we allowed to call
		// enqueue_cell_port, since we're using assertions to check against
		// unintended wires being enqueued into `buf_norm_wire_queue` that
		// would prevent us from restoring the bufnorm invariants in a single
		// pass.

		// We process all explicitly enqueued cell ports (clearing the module level queue).
		for (auto const &[cell, port_name] : buf_norm_cell_port_queue)
			enqueue_cell_port(cell, port_name);
		buf_norm_cell_port_queue.clear();

		// We also enqueue all wires that saw newly added module level connections.
		for (auto &[a, b] : connections_)
			for (auto &sig : {a, b})
				for (auto const &chunk : sig.chunks())
					if (chunk.wire)
						wire_queue_entries(chunk.wire);

		// We then process all wires by processing known driving cell ports
		// (previously buf normalized) and following all `$connect` cells (that
		// have a dedicated module level index while the design is in buf
		// normalized mode).
		while (wire_queue_pos < GetSize(wire_queue_entries)) {
			auto wire = wire_queue_entries[wire_queue_pos++];
			xlog("processing wire %s\n", log_id(wire));

			if (wire->driverCell_) {
				Cell *cell = wire->driverCell_;
				IdString port = wire->driverPort_;
				enqueue_cell_port(cell, port);
			}

			while (true) {
				auto found = buf_norm_connect_index.find(wire);
				if (found == buf_norm_connect_index.end())
					break;
				while (!found->second.empty()) {
					Cell *connect_cell = *found->second.begin();
					log_assert(connect_cell->type == ID($connect));
					SigSpec const &sig_a = connect_cell->getPort(ID::A);
					SigSpec const &sig_b = connect_cell->getPort(ID::B);
					xlog("found $connect cell %s: %s <-> %s\n", log_id(connect_cell), log_signal(sig_a), log_signal(sig_b));
					for (auto &side : {sig_a, sig_b})
						for (auto chunk : side.chunks())
							if (chunk.wire)
								wire_queue_entries(chunk.wire);
					connect(sig_a, sig_b);

					buf_norm_cell_queue.insert(connect_cell);
					remove(connect_cell);
					log_assert(GetSize(buf_norm_wire_queue) <= 2);
					buf_norm_wire_queue.clear();
				}
			}
		}

		// At this point we know all cell ports and wires that need to be
		// re-normalized and know their connectivity is represented by module
		// level connections.

		// As a first step for re-normalization we add all require intermediate
		// wires for cell output and inout ports.
		for (auto &[cell, port] : pending_ports) {
			log_assert(cell->type != ID($input_port));
			log_assert(!cell->type.empty());
			log_assert(!pending_deleted_cells.count(cell));
			SigSpec const &sig = cell->getPort(port);
			Wire *w = addWire(NEW_ID, GetSize(sig));

			// We update the module level connections, `direct_driven_wires`
			// and `direct_driven_wires_conflicts` in such a way that they
			// correspond to what you would get if the intermediate wires had
			// been in place from the beginning.
			connect(sig, w);
			direct_driven_wires.emplace(w, {cell, port});
			cell->setPort(port, w); // Hits the fast path that doesn't enqueue w
			wire_queue_entries(w); // Needed so we pick up the sig <-> w connection
		}

		// At this point we're done with creating wires and know which ones are
		// fully driven by full output ports of existing cells.

		// First we clear the bufnorm data for all processed wires, all of
		// these will be reassigned later, but we use `driverCell_ == nullptr`
		// to keep track of the wires that we still have to update.
		for (auto wire : wire_queue_entries) {
			wire->driverCell_ = nullptr;
			wire->driverPort_.clear();
		}

		// For the unique driving cell ports fully connected to a full wire, we
		// can update the bufnorm data right away. For all other wires we will
		// have to create new `$buf` cells.
		for (auto const &[wire, cellport] : direct_driven_wires) {
			wire->driverCell_ = cellport.first;
			wire->driverPort_ = cellport.second;
		}


		// To create fresh `$buf` cells for all remaining wires, we need to
		// process the module level connectivity to figure out what the input
		// of those `$buf` cells should be and to figure out whether we need
		// any `$connect` cells to represent bidirectional inout connections
		// (or driver conflicts).

		if (yosys_xtrace)
			for (auto const &[lhs, rhs] : connections_)
				xlog("connection %s <-> %s\n", log_signal(lhs), log_signal(rhs));


		// We transfer the connectivity into a sigmap and then clear the module
		// level connections. This forgets about the structure of module level
		// connections, but bufnorm only guarantees that the connectivity as
		// maintained by a `SigMap` is preserved.
		SigMap sigmap(this);
		new_connections({});

		// We pick SigMap representatives by prioritizing input ports over
		// driven wires over other/unknown wires.
		for (bool input_ports : {false, true}) {
			for (auto const &[wire, cellport] : direct_driven_wires) {
				if ((wire->port_input && !wire->port_output) == input_ports) {
					for (int i = 0; i != GetSize(wire); ++i) {
						SigBit driver = SigBit(wire, i);
						sigmap.database.promote(driver);
					}
				}
			}
		}

		// All three pool<SigBit> below are in terms of sigmapped bits
		// Bits that are known to have a unique driver that is an unconditional driver or one or more inout drivers
		pool<SigBit> driven;
		// Bits that have multiple unconditional drivers, this forces the use of `$connect`
		pool<SigBit> conflicted;
		// Bits that are driven by an inout driver
		pool<SigBit> weakly_driven;

		for (auto const &[wire, cellport] : direct_driven_wires) {
			auto const &[cell, port] = cellport;
			for (int i = 0; i != GetSize(wire); ++i) {
				SigBit driver = sigmap(SigBit(wire, i));
				if (cell->type == ID($tribuf) || cell->port_dir(port) == RTLIL::PD_INOUT) {
					// We add inout drivers to `driven` in a separate loop below
					weakly_driven.insert(driver);
				} else {
					// We remove driver conflicts from `driven` in a separate loop below
					bool inserted = driven.insert(driver).second;
					if (!inserted)
						conflicted.insert(driver);
				}
			}
		}

		// If a wire has one or more inout drivers and an unconditional driver, that's still a conflict
		for (auto driver : weakly_driven)
			if (!driven.insert(driver).second)
				conflicted.insert(driver);

		// This only leaves the drivers matching `driven`'s definition above
		for (auto driver : conflicted)
			driven.erase(driver);

		// Having picked representatives and checked whether they are unique
		// drivers, we can turn the connecitivty of our sigmap back into $buf
		// and $connect cells.

		// Module level bitwise connections not representable by `$buf` cells
		pool<pair<SigBit, SigBit>> undirected_connections;

		// Starts out empty but is updated with the connectivity realized by freshly added `$buf` cells
		SigMap buf_connected;

		// For every enqueued wire, we compute a SigSpec of representative
		// drivers. If there are any bits without a unique driver we represent
		// that with `Sz`. If there are multiple drivers for a net, they become
		// connected via `$connect` cells but every wire of the net has the
		// corresponding bit still driven by a buffered `Sz`.
		for (auto wire : wire_queue_entries) {
			SigSpec wire_drivers;
			for (int i = 0; i < GetSize(wire); ++i) {
				SigBit bit(wire, i);
				SigBit mapped = sigmap(bit);
				xlog("bit %s -> mapped %s\n", log_signal(bit), log_signal(mapped));


				buf_connected.apply(bit);
				buf_connected.add(bit, mapped);
				buf_connected.database.promote(mapped);

				if (wire->driverCell_ == nullptr) {
					if (!mapped.is_wire() || driven.count(mapped)) {
						wire_drivers.append(mapped);
						continue;
					} else {
						wire_drivers.append(State::Sz);
					}
				}

				if (bit < mapped)
					undirected_connections.emplace(bit, mapped);
				else if (mapped < bit)
					undirected_connections.emplace(mapped, bit);
			}

			if (wire->driverCell_ == nullptr) {
				xlog("wire %s drivers %s\n", log_id(wire), log_signal(wire_drivers));
				addBuf(NEW_ID, wire_drivers, wire);
			}
		}

		// Finally we group the bitwise connections to emit word-level $connect cells

		static auto sort_key = [](std::pair<SigBit, SigBit> const &p) {
			int first_offset = p.first.is_wire() ? p.first.offset : 0;
			int second_offset = p.second.is_wire() ? p.second.offset : 0;
			return std::make_tuple(p.first.wire, p.second.wire, first_offset - second_offset, p);
		};

		undirected_connections.sort([](std::pair<SigBit, SigBit> const &p, std::pair<SigBit, SigBit> const &q) {
			return sort_key(p) < sort_key(q);
		});

		SigSpec tmp_a, tmp_b;

		for (auto &[bit_a, bit_b] : undirected_connections) {
			tmp_a.append(bit_a);
			tmp_b.append(bit_b);
		}

		xlog("LHS: %s\n", log_signal(tmp_a));
		xlog("RHS: %s\n", log_signal(tmp_b));


		SigSpec sig_a, sig_b;
		SigBit next_a, next_b;

		auto emit_connect_cell = [&]() {
			if (sig_a.empty())
				return;
			xlog("connect %s <-> %s\n", log_signal(sig_a), log_signal(sig_b));
			Cell *connect_cell = addCell(NEW_ID, ID($connect));
			connect_cell->setParam(ID::WIDTH, GetSize(sig_a));
			connect_cell->setPort(ID::A, sig_a);
			connect_cell->setPort(ID::B, sig_b);
			sig_a = SigSpec();
			sig_b = SigSpec();
		};

		for (auto &[bit_a, bit_b] : undirected_connections) {
			if (bit_a == bit_b)
				continue;
			if (bit_a != next_a || bit_b != next_b)
				emit_connect_cell();

			sig_a.append(bit_a);
			sig_b.append(bit_b);
			next_a = bit_a;
			next_b = bit_b;
			if (next_a.is_wire())
				next_a.offset++;
			if (next_b.is_wire())
				next_b.offset++;

		}
		emit_connect_cell();

		buf_norm_cell_queue.clear();

		log_assert(buf_norm_cell_port_queue.empty());
		log_assert(buf_norm_wire_queue.empty());
		log_assert(connections_.empty());
	}

	for (auto cell : pending_deleted_cells) {
		delete cell;
	}
	pending_deleted_cells.clear();
}

void RTLIL::Cell::unsetPort(const RTLIL::IdString& portname)
{
	RTLIL::SigSpec signal;
	auto conn_it = connections_.find(portname);

	if (conn_it != connections_.end())
	{
		for (auto mon : module->monitors)
			mon->notify_connect(this, conn_it->first, conn_it->second, signal);

		if (module->design)
			for (auto mon : module->design->monitors)
				mon->notify_connect(this, conn_it->first, conn_it->second, signal);

		if (yosys_xtrace) {
			log("#X# Unconnect %s.%s.%s\n", log_id(this->module), log_id(this), log_id(portname));
			log_backtrace("-X- ", yosys_xtrace-1);
		}

		if (module->design && module->design->flagBufferedNormalized) {
			if (conn_it->second.is_wire()) {
				Wire *w = conn_it->second.as_wire();
				if (w->driverCell_ == this && w->driverPort_ == portname) {
					w->driverCell_ = nullptr;
					w->driverPort_ = IdString();
					module->buf_norm_wire_queue.insert(w);
				} else if (w->driverCell_) {
					log_assert(w->driverCell_->getPort(w->driverPort_) == w);
				}
			}

			if (type == ID($connect)) {
				for (auto &[port, sig] : connections_) {
					for (auto &chunk : sig.chunks()) {
						if (!chunk.wire)
							continue;
						auto it = module->buf_norm_connect_index.find(chunk.wire);
						if (it == module->buf_norm_connect_index.end())
							continue;
						it->second.erase(this);
						if (it->second.empty())
							module->buf_norm_connect_index.erase(it);
					}
				}
				connections_.erase(conn_it);
				for (auto &[port, sig] : connections_) {
					for (auto &chunk : sig.chunks()) {
						if (!chunk.wire)
							continue;
						module->buf_norm_connect_index[chunk.wire].insert(this);
					}
				}
				return;
			}
		}

		connections_.erase(conn_it);
	}
}

void RTLIL::Cell::setPort(const RTLIL::IdString& portname, RTLIL::SigSpec signal)
{
	auto r = connections_.insert(portname);
	auto conn_it = r.first;
	if (!r.second && conn_it->second == signal)
		return;

	for (auto mon : module->monitors)
		mon->notify_connect(this, conn_it->first, conn_it->second, signal);

	if (module->design)
		for (auto mon : module->design->monitors)
			mon->notify_connect(this, conn_it->first, conn_it->second, signal);

	if (yosys_xtrace) {
		log("#X# Connect %s.%s.%s = %s (%d)\n", log_id(this->module), log_id(this), log_id(portname), log_signal(signal), GetSize(signal));
		log_backtrace("-X- ", yosys_xtrace-1);
	}

	if (module->design && module->design->flagBufferedNormalized)
	{
		// We eagerly clear a driver that got disconnected by changing this port connection
		if (conn_it->second.is_wire()) {
			Wire *w = conn_it->second.as_wire();
			if (w->driverCell_ == this && w->driverPort_ == portname) {
				w->driverCell_ = nullptr;
				w->driverPort_ = IdString();
				module->buf_norm_wire_queue.insert(w);
			}
		}

		auto dir = port_dir(portname);
		// This is a fast path that handles connecting a full driverless wire to an output port,
		// everything else is goes through the bufnorm queues and is handled during the next
		// bufNormalize call
		if ((dir == RTLIL::PD_OUTPUT || dir == RTLIL::PD_INOUT) && signal.is_wire()) {
			Wire *w = signal.as_wire();
			if (w->driverCell_ == nullptr && (
						(w->port_input && !w->port_output) == (type == ID($input_port)))) {
				w->driverCell_ = this;
				w->driverPort_ = portname;

				conn_it->second = std::move(signal);
				return;
			}
		}

		if (dir == RTLIL::PD_OUTPUT || dir == RTLIL::PD_INOUT) {
			module->buf_norm_cell_queue.insert(this);
			module->buf_norm_cell_port_queue.emplace(this, portname);
		} else {
			for (auto &chunk : signal.chunks())
				if (chunk.wire != nullptr && chunk.wire->driverCell_ == nullptr)
					module->buf_norm_wire_queue.insert(chunk.wire);
		}

		if (type == ID($connect)) {
			for (auto &[port, sig] : connections_) {
				for (auto &chunk : sig.chunks()) {
					if (!chunk.wire)
						continue;
					auto it = module->buf_norm_connect_index.find(chunk.wire);
					if (it == module->buf_norm_connect_index.end())
						continue;
					it->second.erase(this);
					if (it->second.empty())
						module->buf_norm_connect_index.erase(it);
				}
			}
			conn_it->second = std::move(signal);
			for (auto &[port, sig] : connections_) {
				for (auto &chunk : sig.chunks()) {
					if (!chunk.wire)
						continue;
					module->buf_norm_connect_index[chunk.wire].insert(this);
				}
			}
			return;
		}
	}
	conn_it->second = std::move(signal);

}

YOSYS_NAMESPACE_END
