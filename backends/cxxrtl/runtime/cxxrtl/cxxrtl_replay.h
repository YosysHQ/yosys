/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2023  Catherine <whitequark@whitequark.org>
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted.
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

#ifndef CXXRTL_REPLAY_H
#define CXXRTL_REPLAY_H

#if !defined(WIN32)
#include <unistd.h>
#define O_BINARY 0
#else
#include <io.h>
#endif

#include <fcntl.h>
#include <cstring>
#include <cstdio>
#include <atomic>
#include <unordered_map>

#include <cxxrtl/cxxrtl.h>
#include <cxxrtl/cxxrtl_time.h>

// Theory of operation
// ===================
//
// Log format
// ----------
//
// The replay log is a simple data format based on a sequence of 32-bit words. The following BNF-like grammar describes
// enough detail to understand the overall structure of the log data and be able to read hex dumps. For a greater
// degree of detail see the source code. The format is considered fully internal to CXXRTL and is subject to change
// without notice.
//
// <file>           ::= <file-header> <definitions> <sample>+
// <file-header>    ::= 0x52585843 0x00004c54
// <definitions>    ::= <packet-define>* <packet-end>
// <sample>         ::= <packet-sample> (<packet-change> | <packet-diag>)* <packet-end>
// <packet-define>  ::= 0xc0000000 ...
// <packet-sample>  ::= 0xc0000001 ...
// <packet-change>  ::= 0x0??????? <chunk>+ | 0x1??????? <index> <chunk>+ | 0x2??????? | 0x3???????
// <chunk>, <index> ::= 0x????????
// <packet-diag>    ::= <packet-break> | <packet-print> | <packet-assert> | <packet-assume>
// <packet-break>   ::= 0xc0000010 <message> <source-location>
// <packet-print>   ::= 0xc0000011 <message> <source-location>
// <packet-assert>  ::= 0xc0000012 <message> <source-location>
// <packet-assume>  ::= 0xc0000013 <message> <source-location>
// <packet-end>     ::= 0xFFFFFFFF
//
// The replay log contains sample data, however, it does not cover the entire design. Rather, it only contains sample
// data for the subset of debug items containing _design state_: inputs and registers/latches. This keeps its size to
// a minimum, and recording speed to a maximum. The player samples any missing data by setting the design state items
// to the same values they had during recording, and re-evaluating the design.
//
// Packets for diagnostics (prints, breakpoints, assertions, and assumptions) are used solely for diagnostics emitted
// by the C++ testbench driving the simulation, and are not recorded while evaluating the design. (Diagnostics emitted
// by the RTL can be reconstructed at replay time, so recording them would be a waste of space.)
//
// Limits
// ------
//
// The log may contain:
//
// * Up to 2**28-1 debug items containing design state.
// * Up to 2**32 chunks per debug item.
// * Up to 2**32 rows per memory.
// * Up to 2**32 samples.
//
// Of these limits, the last two are most likely to be eventually exceeded by practical recordings. However, other
// performance considerations will likely limit the size of such practical recordings first, so the log data format
// will undergo a breaking change at that point.
//
// Operations
// ----------
//
// As suggested by the name "replay log", this format is designed for recording (writing) once and playing (reading)
// many times afterwards, such that reading the format can be done linearly and quickly. The log format is designed to
// support three primary read operations:
//
// 1. Initialization
// 2. Rewinding (to time T)
// 3. Replaying (for N samples)
//
// During initialization, the player establishes the mapping between debug item names and their 28-bit identifiers in
// the log. It is done once.
//
// During rewinding, the player begins reading at the latest non-incremental sample that still lies before the requested
// sample time. It continues reading incremental samples after that point until it reaches the requested sample time.
// This process is very cheap as the design is not evaluated; it is essentially a (convoluted) memory copy operation.
//
// During replaying, the player evaluates the design at the current time, which causes all debug items to assume
// the values they had before recording. This process is expensive. Once done, the player advances to the next state
// by reading the next (complete or incremental) sample, as above. Since a range of samples is replayed, this process
// is repeated several times in a row.
//
// In principle, when replaying, the player could only read the state of the inputs and the time delta and use a normal
// eval/commit loop to progress the simulation, which is fully deterministic so its calculated design state should be
// exactly the same as the recorded design state. In practice, it is both faster and more reliable (in presence of e.g.
// user-defined black boxes) to read the recorded values instead of calculating them.
//
// Note: The operations described above are conceptual and do not correspond exactly to methods on `cxxrtl::player`.
// The `cxxrtl::player::replay()` method does not evaluate the design. This is so that delta cycles could be ignored
// if they are not of interest while replaying.

namespace cxxrtl {

// A single diagnostic that can be manipulated as an object (including being written to and read from a file).
// This differs from the base CXXRTL interface, where diagnostics can only be emitted via a procedure call, and are
// not materialized as objects.
struct diagnostic {
	// The `BREAK` flavor corresponds to a breakpoint, which is a diagnostic type that can currently only be emitted
	// by the C++ testbench code.
	enum flavor {
		BREAK  = 0,
		PRINT  = 1,
		ASSERT = 2,
		ASSUME = 3,
	};

	flavor type;
	std::string message;
	std::string location; // same format as the `src` attribute of `$print` or `$check` cell

	diagnostic()
	: type(BREAK) {}

	diagnostic(flavor type, const std::string &message, const std::string &location)
	: type(type), message(message), location(location) {}

	diagnostic(flavor type, const std::string &message, const char *file, unsigned line)
	: type(type), message(message), location(std::string(file) + ':' + std::to_string(line)) {}
};

// A spool stores CXXRTL design state changes in a file.
class spool {
public:
	// Unique pointer to a specific sample within a replay log. (Timestamps are not unique.)
	typedef uint32_t pointer_t;

	// Numeric identifier assigned to a debug item within a replay log. Range limited to [1, MAXIMUM_IDENT].
	typedef uint32_t ident_t;

	static constexpr uint16_t VERSION = 0x0400;

	static constexpr uint64_t HEADER_MAGIC = 0x00004c5452585843;
	static constexpr uint64_t VERSION_MASK = 0xffff000000000000;

	static constexpr uint32_t PACKET_DEFINE  = 0xc0000000;

	static constexpr uint32_t PACKET_SAMPLE  = 0xc0000001;
	enum sample_flag : uint32_t {
		EMPTY       = 0,
		INCREMENTAL = 1,
	};

	static constexpr uint32_t MAXIMUM_IDENT  = 0x0fffffff;
	static constexpr uint32_t CHANGE_MASK    = 0x30000000;

	static constexpr uint32_t PACKET_CHANGE  = 0x00000000/* | ident */;
	static constexpr uint32_t PACKET_CHANGEI = 0x10000000/* | ident */;
	static constexpr uint32_t PACKET_CHANGEL = 0x20000000/* | ident */;
	static constexpr uint32_t PACKET_CHANGEH = 0x30000000/* | ident */;

	static constexpr uint32_t PACKET_DIAGNOSTIC = 0xc0000010/* | diagnostic::flavor */;
	static constexpr uint32_t DIAGNOSTIC_MASK   = 0x0000000f;

	static constexpr uint32_t PACKET_END     = 0xffffffff;

	// Writing spools.

	class writer {
		int fd;
		size_t position;
		std::vector<uint32_t> buffer;

		// These functions aren't overloaded because of implicit numeric conversions.

		void emit_word(uint32_t word) {
			if (position + 1 == buffer.size())
				flush();
			buffer[position++] = word;
		}

		void emit_dword(uint64_t dword) {
			emit_word(dword >>  0);
			emit_word(dword >> 32);
		}

		void emit_ident(ident_t ident) {
			assert(ident <= MAXIMUM_IDENT);
			emit_word(ident);
		}

		void emit_size(size_t size) {
			assert(size <= std::numeric_limits<uint32_t>::max());
			emit_word(size);
		}

		// Same implementation as `emit_size()`, different declared intent.
		void emit_index(size_t index) {
			assert(index <= std::numeric_limits<uint32_t>::max());
			emit_word(index);
		}

		void emit_string(std::string str) {
			// Align to a word boundary, and add at least one terminating \0.
			str.resize(str.size() + (sizeof(uint32_t) - (str.size() + sizeof(uint32_t)) % sizeof(uint32_t)));
			for (size_t index = 0; index < str.size(); index += sizeof(uint32_t)) {
				uint32_t word;
				memcpy(&word, &str[index], sizeof(uint32_t));
				emit_word(word);
			}
		}

		void emit_time(const time &timestamp) {
			const value<time::bits> &raw_timestamp(timestamp);
			emit_word(raw_timestamp.data[0]);
			emit_word(raw_timestamp.data[1]);
			emit_word(raw_timestamp.data[2]);
		}

	public:
		// Creates a writer, and transfers ownership of `fd`, which must be open for appending.
		//
		// The buffer size is currently fixed to a "reasonably large" size, determined empirically by measuring writer
		// performance on a representative design; large but not so large it would e.g. cause address space exhaustion
		// on 32-bit platforms.
		writer(spool &spool) : fd(spool.take_write()), position(0), buffer(32 * 1024 * 1024) {
			assert(fd != -1);
#if !defined(WIN32)
			int result = ftruncate(fd, 0);
#else
			int result = _chsize_s(fd, 0);
#endif
			assert(result == 0);
		}

		writer(writer &&moved) : fd(moved.fd), position(moved.position), buffer(moved.buffer) {
			moved.fd = -1;
			moved.position = 0;
		}

		writer(const writer &) = delete;
		writer &operator=(const writer &) = delete;

		// Both write() calls and fwrite() calls are too expensive to perform implicitly. The API consumer must determine
		// the optimal time to flush the writer and do that explicitly for best performance.
		void flush() {
			assert(fd != -1);
			size_t data_size = position * sizeof(uint32_t);
			size_t data_written = write(fd, buffer.data(), data_size);
			assert(data_size == data_written);
			position = 0;
		}

		~writer() {
			if (fd != -1) {
				flush();
				close(fd);
			}
		}

		void write_magic() {
			// `CXXRTL` followed by version in binary. This header will read backwards on big-endian machines, which allows
			// detection of this case, both visually and programmatically.
			emit_dword(((uint64_t)VERSION << 48) | HEADER_MAGIC);
		}

		void write_define(ident_t ident, const std::string &name, size_t part_index, size_t chunks, size_t depth) {
			emit_word(PACKET_DEFINE);
			emit_ident(ident);
			emit_string(name);
			emit_index(part_index);
			emit_size(chunks);
			emit_size(depth);
		}

		void write_sample(bool incremental, pointer_t pointer, const time &timestamp) {
			uint32_t flags = (incremental ? sample_flag::INCREMENTAL : 0);
			emit_word(PACKET_SAMPLE);
			emit_word(flags);
			emit_word(pointer);
			emit_time(timestamp);
		}

		void write_change(ident_t ident, size_t chunks, const chunk_t *data) {
			assert(ident <= MAXIMUM_IDENT);

			if (chunks == 1 && *data == 0) {
				emit_word(PACKET_CHANGEL | ident);
			} else if (chunks == 1 && *data == 1) {
				emit_word(PACKET_CHANGEH | ident);
			} else {
				emit_word(PACKET_CHANGE | ident);
				for (size_t offset = 0; offset < chunks; offset++)
					emit_word(data[offset]);
			}
		}

		void write_change(ident_t ident, size_t chunks, const chunk_t *data, size_t index) {
			assert(ident <= MAXIMUM_IDENT);

			emit_word(PACKET_CHANGEI | ident);
			emit_index(index);
			for (size_t offset = 0; offset < chunks; offset++)
				emit_word(data[offset]);
		}

		void write_diagnostic(const diagnostic &diagnostic) {
			emit_word(PACKET_DIAGNOSTIC | diagnostic.type);
			emit_string(diagnostic.message);
			emit_string(diagnostic.location);
		}

		void write_end() {
			emit_word(PACKET_END);
		}
	};

	// Reading spools.

	class reader {
		FILE *f;

		uint32_t absorb_word() {
			// If we're at end of file, `fread` will not write to `word`, and `PACKET_END` will be returned.
			uint32_t word = PACKET_END;
			fread(&word, sizeof(word), 1, f);
			return word;
		}

		uint64_t absorb_dword() {
			uint32_t lo = absorb_word();
			uint32_t hi = absorb_word();
			return ((uint64_t)hi << 32) | lo;
		}

		ident_t absorb_ident() {
			ident_t ident = absorb_word();
			assert(ident <= MAXIMUM_IDENT);
			return ident;
		}

		size_t absorb_size() {
			return absorb_word();
		}

		size_t absorb_index() {
			return absorb_word();
		}

		std::string absorb_string() {
			std::string str;
			do {
				size_t end = str.size();
				str.resize(end + 4);
				uint32_t word = absorb_word();
				memcpy(&str[end], &word, sizeof(uint32_t));
			} while (str.back() != '\0');
			// Strings have no embedded zeroes besides the terminating one(s).
			return str.substr(0, str.find('\0'));
		}

		time absorb_time() {
			value<time::bits> raw_timestamp;
			raw_timestamp.data[0] = absorb_word();
			raw_timestamp.data[1] = absorb_word();
			raw_timestamp.data[2] = absorb_word();
			return time(raw_timestamp);
		}

	public:
		typedef uint64_t pos_t;

		// Creates a reader, and transfers ownership of `fd`, which must be open for reading.
		reader(spool &spool) : f(fdopen(spool.take_read(), "r")) {
			assert(f != nullptr);
		}

		reader(reader &&moved) : f(moved.f) {
			moved.f = nullptr;
		}

		reader(const reader &) = delete;
		reader &operator=(const reader &) = delete;

		~reader() {
			if (f != nullptr)
				fclose(f);
		}

		pos_t position() {
			return ftell(f);
		}

		void rewind(pos_t position) {
			fseek(f, position, SEEK_SET);
		}

		void read_magic() {
			uint64_t magic = absorb_dword();
			assert((magic & ~VERSION_MASK) == HEADER_MAGIC);
			assert((magic >> 48) == VERSION);
		}

		bool read_define(ident_t &ident, std::string &name, size_t &part_index, size_t &chunks, size_t &depth) {
			uint32_t header = absorb_word();
			if (header == PACKET_END)
				return false;
			assert(header == PACKET_DEFINE);
			ident = absorb_ident();
			name = absorb_string();
			part_index = absorb_index();
			chunks = absorb_size();
			depth = absorb_size();
			return true;
		}

		bool read_sample(bool &incremental, pointer_t &pointer, time &timestamp) {
			uint32_t header = absorb_word();
			if (header == PACKET_END)
				return false;
			assert(header == PACKET_SAMPLE);
			uint32_t flags = absorb_word();
			incremental = (flags & sample_flag::INCREMENTAL);
			pointer = absorb_word();
			timestamp = absorb_time();
			return true;
		}

		bool read_header(uint32_t &header) {
			header = absorb_word();
			return header != PACKET_END;
		}

		// This method must be separate from `read_change_data` because `chunks` and `depth` can only be looked up
		// if `ident` is known.
		bool read_change_ident(uint32_t header, ident_t &ident) {
			if ((header & ~(CHANGE_MASK | MAXIMUM_IDENT)) != 0)
				return false; // some other packet
			ident = header & MAXIMUM_IDENT;
			return true;
		}

		void read_change_data(uint32_t header, size_t chunks, size_t depth, chunk_t *data) {
			uint32_t index = 0;
			switch (header & CHANGE_MASK) {
				case PACKET_CHANGEL:
					*data = 0;
					return;
				case PACKET_CHANGEH:
					*data = 1;
					return;
				case PACKET_CHANGE:
					break;
				case PACKET_CHANGEI:
					index = absorb_word();
					assert(index < depth);
					break;
				default:
					assert(false && "Unrecognized change packet");
			}
			for (size_t offset = 0; offset < chunks; offset++)
				data[chunks * index + offset] = absorb_word();
		}

		bool read_diagnostic(uint32_t header, diagnostic &diagnostic) {
			if ((header & ~DIAGNOSTIC_MASK) != PACKET_DIAGNOSTIC)
				return false; // some other packet
			uint32_t type = header & DIAGNOSTIC_MASK;
			assert(type == diagnostic::BREAK  || type == diagnostic::PRINT ||
			       type == diagnostic::ASSERT || type == diagnostic::ASSUME);
			diagnostic.type = (diagnostic::flavor)type;
			diagnostic.message = absorb_string();
			diagnostic.location = absorb_string();
			return true;
		}
	};

	// Opening spools. For certain uses of the record/replay mechanism, two distinct open files (two open files, i.e.
	// two distinct file pointers, and not just file descriptors, which share the file pointer if duplicated) are used,
	// for a reader and writer thread. This class manages the lifetime of the descriptors for these files. When only
	// one of them is used, the other is closed harmlessly when the spool is destroyed.
private:
	std::atomic<int> writefd;
	std::atomic<int> readfd;

public:
	spool(const std::string &filename)
		: writefd(open(filename.c_str(), O_CREAT|O_BINARY|O_WRONLY|O_APPEND, 0644)),
		  readfd(open(filename.c_str(), O_BINARY|O_RDONLY)) {
		assert(writefd.load() != -1 && readfd.load() != -1);
	}

	spool(spool &&moved) : writefd(moved.writefd.exchange(-1)), readfd(moved.readfd.exchange(-1)) {}

	spool(const spool &) = delete;
	spool &operator=(const spool &) = delete;

	~spool() {
		int fd;
		if ((fd = writefd.exchange(-1)) != -1)
			close(fd);
		if ((fd = readfd.exchange(-1)) != -1)
			close(fd);
	}

	// Atomically acquire a write file descriptor for the spool. Can be called once, and will return -1 the next time
	// it is called. Thread-safe.
	int take_write() {
		return writefd.exchange(-1);
	}

	// Atomically acquire a read file descriptor for the spool. Can be called once, and will return -1 the next time
	// it is called. Thread-safe.
	int take_read() {
		return readfd.exchange(-1);
	}
};

// A CXXRTL recorder samples design state, producing complete or incremental updates, and writes them to a spool.
class recorder {
	struct variable {
		spool::ident_t ident; /* <= spool::MAXIMUM_IDENT */
		size_t chunks;
		size_t depth; /* == 1 for wires */
		chunk_t *curr;
		bool memory;
	};

	spool::writer writer;
	std::vector<variable> variables;
	std::vector<size_t> inputs; // values of inputs must be recorded explicitly, as their changes are not observed
	std::unordered_map<const chunk_t*, spool::ident_t> ident_lookup;
	bool streaming = false; // whether variable definitions have been written
	spool::pointer_t pointer = 0;
	time timestamp;

public:
	template<typename ...Args>
	recorder(Args &&...args) : writer(std::forward<Args>(args)...) {}

	void start(module &module, std::string top_path = "") {
		debug_items items;
		module.debug_info(&items, /*scopes=*/nullptr, top_path);
		start(items);
	}

	void start(const debug_items &items) {
		assert(!streaming);

		writer.write_magic();
		for (auto item : items.table)
			for (size_t part_index = 0; part_index < item.second.size(); part_index++) {
				auto &part = item.second[part_index];
				if ((part.flags & debug_item::INPUT) || (part.flags & debug_item::DRIVEN_SYNC) ||
						(part.type == debug_item::MEMORY)) {
					variable var;
					var.ident = variables.size() + 1;
					var.chunks = (part.width + sizeof(chunk_t) * 8 - 1) / (sizeof(chunk_t) * 8);
					var.depth = part.depth;
					var.curr = part.curr;
					var.memory = (part.type == debug_item::MEMORY);
					ident_lookup[var.curr] = var.ident;

					assert(variables.size() < spool::MAXIMUM_IDENT);
					if (part.flags & debug_item::INPUT)
						inputs.push_back(variables.size());
					variables.push_back(var);

					writer.write_define(var.ident, item.first, part_index, var.chunks, var.depth);
				}
			}
		writer.write_end();
		streaming = true;
	}

	const time &latest_time() {
		return timestamp;
	}

	const time &advance_time(const time &delta) {
		assert(!delta.is_negative());
		timestamp += delta;
		return timestamp;
	}

	void record_complete() {
		assert(streaming);

		writer.write_sample(/*incremental=*/false, pointer++, timestamp);
		for (auto var : variables) {
			assert(var.ident != 0);
			if (!var.memory)
				writer.write_change(var.ident, var.chunks, var.curr);
			else
				for (size_t index = 0; index < var.depth; index++)
					writer.write_change(var.ident, var.chunks, &var.curr[var.chunks * index], index);
		}
		writer.write_end();
	}

	// This function is generic over ModuleT to encourage observer callbacks to be inlined into the commit function.
	template<class ModuleT>
	bool record_incremental(ModuleT &module) {
		assert(streaming);

		struct : observer {
			std::unordered_map<const chunk_t*, spool::ident_t> *ident_lookup;
			spool::writer *writer;

			CXXRTL_ALWAYS_INLINE
			void on_update(size_t chunks, const chunk_t *base, const chunk_t *value) {
				writer->write_change(ident_lookup->at(base), chunks, value);
			}

			CXXRTL_ALWAYS_INLINE
			void on_update(size_t chunks, const chunk_t *base, const chunk_t *value, size_t index) {
				writer->write_change(ident_lookup->at(base), chunks, value, index);
			}
		} record_observer;
		record_observer.ident_lookup = &ident_lookup;
		record_observer.writer = &writer;

		writer.write_sample(/*incremental=*/true, pointer++, timestamp);
		for (auto input_index : inputs) {
			variable &var = variables.at(input_index);
			assert(!var.memory);
			writer.write_change(var.ident, var.chunks, var.curr);
		}
		bool changed = module.commit(record_observer);
		writer.write_end();
		return changed;
	}

	void record_diagnostic(const diagnostic &diagnostic) {
		assert(streaming);

		// Emit an incremental delta cycle per diagnostic to simplify the logic of the recorder. This is inefficient, but
		// diagnostics should be rare enough that this inefficiency does not matter. If it turns out to be an issue, this
		// code should be changed to accumulate diagnostics to a buffer that is flushed in `record_{complete,incremental}`
		// and also in `advance_time` before the timestamp is changed. (Right now `advance_time` never writes to the spool.)
		writer.write_sample(/*incremental=*/true, pointer++, timestamp);
		writer.write_diagnostic(diagnostic);
		writer.write_end();
	}

	void flush() {
		writer.flush();
	}
};

// A CXXRTL player reads samples from a spool, and changes the design state accordingly. To start reading samples,
// a spool must have been initialized: the recorder must have been started and an initial complete sample must have
// been written.
class player {
	struct variable {
		size_t chunks;
		size_t depth; /* == 1 for wires */
		chunk_t *curr;
	};

	spool::reader reader;
	std::unordered_map<spool::ident_t, variable> variables;
	bool streaming = false; // whether variable definitions have been read
	bool initialized = false; // whether a sample has ever been read
	spool::pointer_t pointer = 0;
	time timestamp;

	std::map<spool::pointer_t, spool::reader::pos_t, std::greater<spool::pointer_t>> index_by_pointer;
	std::map<time, spool::reader::pos_t, std::greater<time>> index_by_timestamp;

	bool peek_sample(spool::pointer_t &pointer, time &timestamp) {
		bool incremental;
		auto position = reader.position();
		bool success = reader.read_sample(incremental, pointer, timestamp);
		reader.rewind(position);
		return success;
	}

public:
	template<typename ...Args>
	player(Args &&...args) : reader(std::forward<Args>(args)...) {}

	// The `top_path` must match the one given to the recorder.
	void start(module &module, std::string top_path = "") {
		debug_items items;
		module.debug_info(&items, /*scopes=*/nullptr, top_path);
		start(items);
	}

	void start(const debug_items &items) {
		assert(!streaming);

		reader.read_magic();
		while (true) {
			spool::ident_t ident;
			std::string name;
			size_t part_index;
			size_t chunks;
			size_t depth;
			if (!reader.read_define(ident, name, part_index, chunks, depth))
				break;
			assert(variables.count(ident) == 0);
			assert(items.count(name) != 0);
			assert(part_index < items.count(name));

			const debug_item &part = items.at(name).at(part_index);
			assert(chunks == (part.width + sizeof(chunk_t) * 8 - 1) / (sizeof(chunk_t) * 8));
			assert(depth == part.depth);

			variable &var = variables[ident];
			var.chunks = chunks;
			var.depth = depth;
			var.curr = part.curr;
		}
		assert(variables.size() > 0);
		streaming = true;

		// Establish the initial state of the design.
		std::vector<diagnostic> diagnostics;
		initialized = replay(&diagnostics);
		assert(initialized && diagnostics.empty());
	}

	// Returns the pointer of the current sample.
	spool::pointer_t current_pointer() {
		assert(initialized);
		return pointer;
	}

	// Returns the time of the current sample.
	const time &current_time() {
		assert(initialized);
		return timestamp;
	}

	// Returns `true` if there is a next sample to read, and sets `pointer` to its pointer if there is.
	bool get_next_pointer(spool::pointer_t &pointer) {
		assert(streaming);
		time timestamp;
		return peek_sample(pointer, timestamp);
	}

	// Returns `true` if there is a next sample to read, and sets `timestamp` to its time if there is.
	bool get_next_time(time &timestamp) {
		assert(streaming);
		uint32_t pointer;
		return peek_sample(pointer, timestamp);
	}

	// If this function returns `true`, then `current_pointer() == at_pointer`, and the module contains values that
	// correspond to this pointer in the replay log. To obtain a valid pointer, call `current_pointer()`; while pointers
	// are monotonically increasing for each consecutive sample, using arithmetic operations to create a new pointer is
	// not allowed. The `diagnostics` argument, if not `nullptr`, receives the diagnostics recorded in this sample.
	bool rewind_to(spool::pointer_t at_pointer, std::vector<diagnostic> *diagnostics) {
		assert(initialized);

		// The pointers in the replay log start from one that is greater than `at_pointer`. In this case the pointer will
		// never be reached.
		assert(index_by_pointer.size() > 0);
		if (at_pointer < index_by_pointer.rbegin()->first)
			return false;

		// Find the last complete sample whose pointer is less than or equal to `at_pointer`. Note that the comparison
		// function used here is `std::greater`, inverting the direction of `lower_bound`.
		auto position_it = index_by_pointer.lower_bound(at_pointer);
		assert(position_it != index_by_pointer.end());
		reader.rewind(position_it->second);

		// Replay samples until eventually arriving to `at_pointer` or encountering end of file.
		while(replay(diagnostics)) {
			if (pointer == at_pointer)
				return true;

			if (diagnostics)
				diagnostics->clear();
		}
		return false;
	}

	// If this function returns `true`, then `current_time() <= at_or_before_timestamp`, and the module contains values
	// that correspond to `current_time()` in the replay log. If `current_time() == at_or_before_timestamp` and there
	// are several consecutive samples with the same time, the module contains values that correspond to the first of
	// these samples. The `diagnostics` argument, if not `nullptr`, receives the diagnostics recorded in this sample.
	bool rewind_to_or_before(const time &at_or_before_timestamp, std::vector<diagnostic> *diagnostics) {
		assert(initialized);

		// The timestamps in the replay log start from one that is greater than `at_or_before_timestamp`. In this case
		// the timestamp will never be reached. Otherwise, this function will always succeed.
		assert(index_by_timestamp.size() > 0);
		if (at_or_before_timestamp < index_by_timestamp.rbegin()->first)
			return false;

		// Find the last complete sample whose timestamp is less than or equal to `at_or_before_timestamp`. Note that
		// the comparison function used here is `std::greater`, inverting the direction of `lower_bound`.
		auto position_it = index_by_timestamp.lower_bound(at_or_before_timestamp);
		assert(position_it != index_by_timestamp.end());
		reader.rewind(position_it->second);

		// Replay samples until eventually arriving to or past `at_or_before_timestamp` or encountering end of file.
		while (replay(diagnostics)) {
			if (timestamp == at_or_before_timestamp)
				break;

			time next_timestamp;
			if (!get_next_time(next_timestamp))
				break;
			if (next_timestamp > at_or_before_timestamp)
				break;

			if (diagnostics)
				diagnostics->clear();
		}
		return true;
	}

	// If this function returns `true`, then `current_pointer()` and `current_time()` are updated for the next sample
	// and the module now contains values that correspond to that sample. If it returns `false`, there was no next sample
	// to read. The `diagnostics` argument, if not `nullptr`, receives the diagnostics recorded in the next sample.
	bool replay(std::vector<diagnostic> *diagnostics) {
		assert(streaming);

		bool incremental;
		auto position = reader.position();
		if (!reader.read_sample(incremental, pointer, timestamp))
			return false;

		// The very first sample that is read must be a complete sample. This is required for the rewind functions to work.
		assert(initialized || !incremental);

		// It is possible (though not very useful) to have several complete samples with the same timestamp in a row.
		// Ensure that we associate the timestamp with the position of the first such complete sample. (This condition
		// works because the player never jumps over a sample.)
		if (!incremental && !index_by_pointer.count(pointer)) {
			assert(!index_by_timestamp.count(timestamp));
			index_by_pointer[pointer] = position;
			index_by_timestamp[timestamp] = position;
		}

		uint32_t header;
		while (reader.read_header(header)) {
			spool::ident_t ident;
			diagnostic diag;
			if (reader.read_change_ident(header, ident)) {
				variable &var = variables.at(ident);
				reader.read_change_data(header, var.chunks, var.depth, var.curr);
			} else if (reader.read_diagnostic(header, diag)) {
				if (diagnostics)
					diagnostics->push_back(diag);
			} else assert(false && "Unrecognized packet header");
		}
		return true;
	}
};

}

#endif
