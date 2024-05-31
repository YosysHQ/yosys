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

#ifndef DRIVERTOOLS_H
#define DRIVERTOOLS_H

#include <type_traits>

#include "kernel/rtlil.h"
#include "kernel/sigtools.h"
#include "kernel/celltypes.h"

YOSYS_NAMESPACE_BEGIN

struct DriveBit;

struct DriveChunkWire;
struct DriveChunkPort;
struct DriveChunkMarker;
struct DriveChunk;

struct DriveSpec;

const char *log_signal(DriveChunkWire const &chunk);
const char *log_signal(DriveChunkPort const &chunk);
const char *log_signal(DriveChunkMarker const &chunk);
const char *log_signal(DriveChunk const &chunk);
const char *log_signal(DriveSpec const &chunk);

enum class DriveType : unsigned char
  {
    NONE,
    CONSTANT,
    WIRE,
    PORT,
    MULTIPLE,
    MARKER,
  };

struct DriveBitWire
{
  Wire *wire;
  int offset;

  DriveBitWire(Wire *wire, int offset);

  bool operator==(const DriveBitWire &other) const;

  bool operator<(const DriveBitWire &other) const;

  unsigned int hash() const;

  operator SigBit() const;
};

struct DriveBitPort
{
  Cell *cell;
  IdString port;
  int offset;

  DriveBitPort(Cell *cell, IdString port, int offset);

  bool operator==(const DriveBitPort &other) const;

  bool operator<(const DriveBitPort &other) const;

  unsigned int hash() const;
};

struct DriveBitMarker
{
  int marker;
  int offset;

  DriveBitMarker(int marker, int offset);

  bool operator==(const DriveBitMarker &other) const;

  bool operator<(const DriveBitMarker &other) const;

  unsigned int hash() const;
};

struct DriveBitMultiple
{
private:
  pool<DriveBit> multiple_;

public:
  DriveBitMultiple();
  DriveBitMultiple(DriveBit const &single);

  pool<DriveBit> const &multiple() const;

  void merge(DriveBitMultiple const &other);
  void merge(DriveBitMultiple &&other);
  void merge(DriveBit const &single);
  void merge(DriveBit &&single);

  bool operator==(const DriveBitMultiple &other) const;

  unsigned int hash() const;
};

struct DriveBit
{
private:
  DriveType type_ = DriveType::NONE;
  union
  {
    State constant_;
    DriveBitWire wire_;
    DriveBitPort port_;
    DriveBitMarker marker_;
    DriveBitMultiple multiple_;
  };

public:
  DriveBit();

  DriveBit(SigBit const &bit);

  DriveBit(DriveBit const &other);
  DriveBit(DriveBit &&other);

  DriveBit(State constant);
  DriveBit(DriveBitWire const &wire);
  DriveBit(DriveBitWire &&wire);
  DriveBit(DriveBitPort const &port);
  DriveBit(DriveBitPort &&port);
  DriveBit(DriveBitMarker const &marker);
  DriveBit(DriveBitMarker &&marker);
  DriveBit(DriveBitMultiple const &multiple);
  DriveBit(DriveBitMultiple &&multiple);

  ~DriveBit();

  void set_none();

  DriveBit &operator=(DriveBit const &other);
  DriveBit &operator=(DriveBit &&other);

  DriveBit &operator=(State constant);
  DriveBit &operator=(DriveBitWire const &wire);
  DriveBit &operator=(DriveBitWire &&wire);
  DriveBit &operator=(DriveBitPort const &port);
  DriveBit &operator=(DriveBitPort &&port);
  DriveBit &operator=(DriveBitMarker const &marker);
  DriveBit &operator=(DriveBitMarker &&marker);
  DriveBit &operator=(DriveBitMultiple const &multiple);
  DriveBit &operator=(DriveBitMultiple &&multiple);

  unsigned int hash() const;

  bool operator==(const DriveBit &other) const;
  bool operator!=(const DriveBit &other) const;

  bool operator<(const DriveBit &other) const;

  DriveType type() const;

  bool is_none() const;
  bool is_constant() const;
  bool is_wire() const;
  bool is_port() const;
  bool is_marker() const;
  bool is_multiple() const;

  State &constant();
  State const &constant() const;
  DriveBitWire &wire();
  DriveBitWire const &wire() const;
  DriveBitPort &port();
  DriveBitPort const &port() const;
  DriveBitMarker &marker();
  DriveBitMarker const &marker() const;
  DriveBitMultiple &multiple();
  DriveBitMultiple const &multiple() const;

  void merge(DriveBit const &other);
};

struct DriveChunkWire
{
  Wire *wire;
  int offset;
  int width;

  DriveChunkWire(Wire *wire, int offset, int width);
  DriveChunkWire(DriveBitWire const &bit);

  int size() const;
  DriveBitWire operator[](int i) const;
  bool can_append(DriveBitWire const &bit) const;
  bool try_append(DriveBitWire const &bit);
  bool try_append(DriveChunkWire const &chunk);
  bool is_whole() const;
  bool operator==(const DriveChunkWire &other) const;
  bool operator<(const DriveChunkWire &other) const;
  unsigned int hash() const;
  explicit operator SigChunk() const;
};

struct DriveChunkPort
{
  Cell *cell;
  IdString port;
  int offset;
  int width;

  DriveChunkPort(Cell *cell, IdString port, int offset, int width);
  DriveChunkPort(Cell *cell, IdString port);
  DriveChunkPort(Cell *cell, std::pair<IdString, SigSpec> const &conn);
  DriveChunkPort(DriveBitPort const &bit);

  int size() const;
  DriveBitPort operator[](int i) const;
  bool can_append(DriveBitPort const &bit) const;
  bool try_append(DriveBitPort const &bit);
  bool try_append(DriveChunkPort const &chunk);
  bool is_whole() const;
  bool operator==(const DriveChunkPort &other) const;
  bool operator<(const DriveChunkPort &other) const;
  unsigned int hash() const;
};

struct DriveChunkMarker
{
  int marker;
  int offset;
  int width;

  DriveChunkMarker(int marker, int offset, int width);
  DriveChunkMarker(DriveBitMarker const &bit);

  int size() const;
  DriveBitMarker operator[](int i) const;
  bool can_append(DriveBitMarker const &bit) const;
  bool try_append(DriveBitMarker const &bit);
  bool try_append(DriveChunkMarker const &chunk);
  bool operator==(const DriveChunkMarker &other) const;
  bool operator<(const DriveChunkMarker &other) const;
  unsigned int hash() const;
};

struct DriveChunkMultiple
{
private:
  mutable pool<DriveChunk> multiple_;
  int width_;

public:
  pool<DriveChunk> const &multiple() const;

  DriveChunkMultiple(DriveBitMultiple const &bit);

  int size() const;
  DriveBitMultiple operator[](int i) const;
  bool can_append(DriveBitMultiple const &bit) const;
  bool try_append(DriveBitMultiple const &bit);
  bool can_append(DriveChunkMultiple const &bit) const;
  bool try_append(DriveChunkMultiple const &bit);
  bool operator==(const DriveChunkMultiple &other) const;
  bool operator<(const DriveChunkMultiple &other) const;
  unsigned int hash() const;
};

struct DriveChunk
{
private:
  DriveType type_ = DriveType::NONE;
  union
  {
    int none_;
    Const constant_;
    DriveChunkWire wire_;
    DriveChunkPort port_;
    DriveChunkMarker marker_;
    DriveChunkMultiple multiple_;
  };

public:
  DriveChunk();
  DriveChunk(DriveChunk const &other);
  DriveChunk(DriveChunk &&other);
  DriveChunk(DriveBit const &other);
  DriveChunk(Const const &constant);
  DriveChunk(Const &&constant);
  DriveChunk(DriveChunkWire const &wire);
  DriveChunk(DriveChunkWire &&wire);
  DriveChunk(DriveChunkPort const &port);
  DriveChunk(DriveChunkPort &&port);
  DriveChunk(DriveChunkMarker const &marker);
  DriveChunk(DriveChunkMarker &&marker);
  DriveChunk(DriveChunkMultiple const &multiple);
  DriveChunk(DriveChunkMultiple &&multiple);
  ~DriveChunk();

  DriveBit operator[](int i) const;
  void set_none(int width = 0);
  DriveChunk &operator=(DriveChunk const &other);
  DriveChunk &operator=(DriveChunk &&other);
  DriveChunk &operator=(Const const &constant);
  DriveChunk &operator=(Const &&constant);
  DriveChunk &operator=(DriveChunkWire const &wire);
  DriveChunk &operator=(DriveChunkWire &&wire);
  DriveChunk &operator=(DriveChunkPort const &port);
  DriveChunk &operator=(DriveChunkPort &&port);
  DriveChunk &operator=(DriveChunkMarker const &marker);
  DriveChunk &operator=(DriveChunkMarker &&marker);
  DriveChunk &operator=(DriveChunkMultiple const &multiple);
  DriveChunk &operator=(DriveChunkMultiple &&multiple);
  DriveChunk &operator=(DriveBit const &other);
  bool can_append(DriveBit const &bit) const;
  bool try_append(DriveBit const &bit);
  bool try_append(DriveChunk const &chunk);
  unsigned int hash() const;
  bool operator==(const DriveChunk &other) const;
  bool operator!=(const DriveChunk &other) const;
  bool operator<(const DriveChunk &other) const;
  DriveType type() const;
  bool is_none() const;
  bool is_constant() const;
  bool is_wire() const;
  bool is_port() const;
  bool is_marker() const;
  bool is_multiple() const;
  Const &constant();
  Const const &constant() const;
  DriveChunkWire &wire();
  DriveChunkWire const &wire() const;
  DriveChunkPort &port();
  DriveChunkPort const &port() const;
  DriveChunkMarker &marker();
  DriveChunkMarker const &marker() const;
  DriveChunkMultiple &multiple();
  DriveChunkMultiple const &multiple() const;
  int size() const;
};

struct DriveSpec
{
private:
  int width_ = 0;
  mutable std::vector<DriveChunk> chunks_;
  mutable std::vector<DriveBit> bits_;
  mutable unsigned int hash_ = 0;

public:
  inline bool packed() const;
    
  DriveSpec();
  DriveSpec(DriveChunk const &chunk);
  DriveSpec(DriveChunkWire const &chunk);
  DriveSpec(DriveChunkPort const &chunk);
  DriveSpec(DriveChunkMarker const &chunk);
  DriveSpec(DriveChunkMultiple const &chunk);

  DriveSpec(DriveBit const &bit);
  DriveSpec(DriveBitWire const &bit);
  DriveSpec(DriveBitPort const &bit);
  DriveSpec(DriveBitMarker const &bit);
  DriveSpec(DriveBitMultiple const &bit);

  DriveSpec(std::vector<DriveChunk> const &chunks);
  DriveSpec(std::vector<DriveBit> const &bits);

  std::vector<DriveChunk> const &chunks() const;
  std::vector<DriveBit> const &bits() const;

  int size() const;

  void append(DriveBit const &bit);
  void append(DriveChunk const &chunk);

  void pack() const;
  void unpack() const;

  DriveBit &operator[](int index);
  const DriveBit &operator[](int index) const;

  void clear();

  DriveSpec &operator=(DriveChunk const &chunk);
  DriveSpec &operator=(DriveChunkWire const &chunk);
  DriveSpec &operator=(DriveChunkPort const &chunk);
  DriveSpec &operator=(DriveChunkMarker const &chunk);
  DriveSpec &operator=(DriveChunkMultiple const &chunk);

  DriveSpec &operator=(DriveBit const &bit);
  DriveSpec &operator=(DriveBitWire const &bit);
  DriveSpec &operator=(DriveBitPort const &bit);
  DriveSpec &operator=(DriveBitMarker const &bit);
  DriveSpec &operator=(DriveBitMultiple const &bit);

  unsigned int hash() const;

  bool operator==(DriveSpec const &other) const;

private:
  void compute_width();
};

struct DriverMap
{
  CellTypes celltypes;

  DriverMap();
  DriverMap(Design *design);

private:
  
  // Internally we represent all DriveBits by mapping them to DriveBitIds
  // which use less memory and are cheaper to compare.
  struct DriveBitId
  {
    int id;

    DriveBitId();
    DriveBitId(int id);

    bool operator==(const DriveBitId &other) const;
    bool operator!=(const DriveBitId &other) const;
    bool operator<(const DriveBitId &other) const;
    unsigned int hash() const;
  };

  // Essentially a dict<DriveBitId, pool<DriveBitId>> but using less memory
  // and fewer allocations
  struct DriveBitGraph
  {
    dict<DriveBitId, DriveBitId> first_edges;
    dict<DriveBitId, DriveBitId> second_edges;
    dict<DriveBitId, pool<DriveBitId>> more_edges;

    void add_edge(DriveBitId src, DriveBitId dst);
    DriveBitId pop_edge(DriveBitId src);
    void clear(DriveBitId src);
    bool contains(DriveBitId src);
    int count(DriveBitId src);
    DriveBitId at(DriveBitId src, int index);
  };

  
  // The following two maps maintain a sparse DriveBit to DriveBitId mapping.
  // This saves a lot of memory compared to a `dict<DriveBit, DriveBitId>` or
  // `idict<DriveBit>`.

  // Maps wires to the first DriveBitId of the consecutive range used for
  // that wire.
  dict<Wire *, DriveBitId> wire_offsets;

  // Maps cell ports to a the first DriveBitId of the consecutive range used
  // for that cell port.
  dict<pair<Cell *, IdString>, DriveBitId> port_offsets;

  // For the inverse map that maps DriveBitIds back to DriveBits we use a
  // sorted map containing only the first DriveBit for each wire and cell
  // port.
  std::map<DriveBitId, DriveBit> drive_bits;

  // As a memory optimization for gate level net lists we store single-bit
  // wires and cell ports in a `dict` which requires less memory and fewer
  // allocations than `std::map` but doesn't support the kind of lookups we
  // need for a sparse coarse grained mapping.
  dict<DriveBitId, DriveBit> isolated_drive_bits;

  // Used for allocating DriveBitIds, none and constant states use a fixewd
  // mapping to the first few ids, which we need to skip.
  int next_offset = 1 + (int)State::Sm;

  // Union-Find over directly connected bits that share the same single
  // driver or are undriven. We never merge connections between drivers
  // and/or kept wires.
  mfp<DriveBitId> same_driver;

  // For each bit, store a set of connected driver bits for which the
  // explicit connection should be preserved and the driving direction is
  // locally unambiguous (one side only drives or requires a driven value).
  DriveBitGraph connected_drivers;

  // For each bit, store a set of connected driver bits for which the
  // explicit connection should be preserved and the driving direction is
  // locally ambiguous. Every such ambiguous connection is also present in
  // the reverse direction and has to be resolved when querying drivers.
  DriveBitGraph connected_undirected;

  // Subset of `connected_undirected` for caching the resolved driving
  // direction. In case multiple drivers are present this can still contain
  // both orientations of a single connection, but for a single driver only
  // one will be present.
  DriveBitGraph connected_oriented;

  // Stores for which bits we already resolved the orientation (cached in
  // `connected_oriented`).
  pool<DriveBitId> oriented_present;
  
  enum class BitMode {
    NONE = 0, // Not driven, no need to keep wire
    DRIVEN = 1, // Not driven, uses a value driven elsewhere
    DRIVEN_UNIQUE = 2, // Uses a value driven elsewhere, has at most one direct connection
    KEEP = 3, // Wire that should be kept
    TRISTATE = 4, // Can drive a value but can also use a value driven elsewhere
    DRIVER = 5, // Drives a value
  };

  BitMode bit_mode(DriveBit const &bit);
  DriveBitId id_from_drive_bit(DriveBit const &bit);
  DriveBit drive_bit_from_id(DriveBitId id);
  void connect_directed_merge(DriveBitId driven_id, DriveBitId driver_id);
  void connect_directed_buffer(DriveBitId driven_id, DriveBitId driver_id);
  void connect_undirected(DriveBitId a_id, DriveBitId b_id);
  void add_port(Cell *cell, IdString const &port, SigSpec const &b);
  void orient_undirected(DriveBitId id);
  bool keep_wire(Wire *wire);
  
  // Only used a local variables in `orient_undirected`, always cleared, only
  // stored to reduce allocations.
  pool<DriveBitId> orient_undirected_seen;
  pool<DriveBitId> orient_undirected_drivers;
  dict<DriveBitId, int> orient_undirected_distance;

  
public:
  void add(Module *module);
  void add(DriveBit const &a, DriveBit const &b);

  
  template<typename T>
  static constexpr bool is_sig_type() {
    return
      std::is_same<T, SigSpec>::value ||
      std::is_same<T, SigChunk>::value ||
      std::is_same<T, DriveSpec>::value ||
      std::is_same<T, DriveChunk>::value ||
      std::is_same<T, DriveChunkPort>::value ||
      std::is_same<T, DriveChunkWire>::value ||
      std::is_same<T, Const>::value;
  }

  // We use the enable_if to produce better compiler errors when unsupported
  // types are used
  template<typename T, typename U>
  typename std::enable_if<is_sig_type<T>() && is_sig_type<U>()>::type
  add(T const &a, U const &b)
  {
    log_assert(a.size() == b.size());
    for (int i = 0; i != GetSize(a); ++i)
      add(DriveBit(a[i]), DriveBit(b[i]));
  }
  
  // Specialized version that avoids unpacking
  void add(SigSpec const &a, SigSpec const &b);
  DriveBit operator()(DriveBit const &bit);
  DriveSpec operator()(DriveSpec spec);
};

YOSYS_NAMESPACE_END

#endif
