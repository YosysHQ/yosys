#
# yosys -- Yosys Open SYnthesis Suite
#
# Copyright (C) 2022  Jannis Harder <jix@yosyshq.com> <me@jix.one>
#
# Permission to use, copy, modify, and/or distribute this software for any
# purpose with or without fee is hereby granted, provided that the above
# copyright notice and this permission notice appear in all copies.
#
# THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
# WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
# MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
# ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
# WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
# ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
# OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
#

import json, re

from functools import total_ordering


class PrettyJson:
    def __init__(self, f):
        self.f = f
        self.indent = 0
        self.state = ["value"]

    def line(self):
        indent = len(self.state) - bool(self.state and self.state[-1] == "value")
        print("\n", end=" " * (2 * indent), file=self.f)

    def raw(self, str):
        print(end=str, file=self.f)

    def begin_object(self):
        self.begin_value()
        self.raw("{")
        self.state.append("object_first")

    def begin_array(self):
        self.begin_value()
        self.raw("[")
        self.state.append("array_first")

    def end_object(self):
        state = self.state.pop()
        if state == "object":
            self.line()
        else:
            assert state == "object_first"
        self.raw("}")
        self.end_value()

    def end_array(self):
        state = self.state.pop()
        if state == "array":
            self.line()
        else:
            assert state == "array_first"
        self.raw("]")
        self.end_value()

    def name(self, name):
        if self.state[-1] == "object_first":
            self.state[-1] = "object"
        else:
            self.raw(",")
        self.line()
        json.dump(str(name), self.f)
        self.raw(": ")
        self.state.append("value")

    def begin_value(self):
        if self.state[-1] == "array_first":
            self.line()
            self.state[-1] = "array"
        elif self.state[-1] == "array":
            self.raw(",")
            self.line()
        else:
            assert self.state.pop() == "value"

    def end_value(self):
        if not self.state:
            print(file=self.f, flush=True)

    def value(self, value):
        self.begin_value()
        json.dump(value, self.f)
        self.end_value()

    def entry(self, name, value):
        self.name(name)
        self.value(value)

    def object(self, entries=None):
        if isinstance(entries, dict):
            entries = dict.items()
        self.begin_object()
        for name, value in entries:
            self.entry(name, value)
        self.end_object()

    def array(self, values=None):
        self.begin_array()
        for value in values:
            self.value(value)
        self.end_array()


addr_re = re.compile(r'\\\[[0-9]+\]$')
public_name_re = re.compile(r"\\([a-zA-Z_][a-zA-Z0-9_]*(\[[0-9]+\])?|\[[0-9]+\])$")

def pretty_name(id):
    if public_name_re.match(id):
        return id.lstrip("\\")
    else:
        return id

def pretty_path(path):
    out = ""
    for name in path:
        name = pretty_name(name)
        if name.startswith("["):
            out += name
            continue
        if out:
            out += "."
        if name.startswith("\\") or name.startswith("$"):
            out += name + " "
        else:
            out += name

    return out

@total_ordering
class WitnessSig:
    def __init__(self, path, offset, width=1, init_only=False):
        path = tuple(path)
        self.path, self.width, self.offset, self.init_only = path, width, offset, init_only

        self.memory_path = None
        self.memory_addr = None

        sort_path = path
        sort_id = -1
        if path and addr_re.match(path[-1]):
            self.memory_path = sort_path = path[:-1]
            self.memory_addr = sort_id = int(path[-1][2:-1])

        self.sort_key = (init_only, sort_path, sort_id, offset, width)

    def bits(self):
        return ((self.path, i) for i in range(self.offset, self.offset + self.width))

    def rev_bits(self):
        return ((self.path, i) for i in reversed(range(self.offset, self.offset + self.width)))

    def pretty(self):
        if self.width > 1:
            last_offset = self.offset + self.width - 1
            return f"{pretty_path(self.path)}[{last_offset}:{self.offset}]"
        else:
            return f"{pretty_path(self.path)}[{self.offset}]"

    def __eq__(self):
        return self.sort_key

    def __hash__(self):
        return hash(self.sort_key)

    def __lt__(self, other):
        return self.sort_key < other.sort_key


def coalesce_signals(signals, bits=None):
    if bits is None:
        bits = {}
    for sig in signals:
        for bit in sig.bits():
            if sig.init_only:
                bits.setdefault(bit, False)
            else:
                bits[bit] = True

    active = None

    out = []

    for bit, not_init in sorted(bits.items()):
        if active:
            if active[0] == bit[0] and active[2] == bit[1] and active[3] == not_init:
                active[2] += 1
            else:
                out.append(WitnessSig(active[0], active[1], active[2] - active[1], not active[3]))
                active = None

        if active is None:
            active = [bit[0], bit[1], bit[1] + 1, not_init]

    if active:
        out.append(WitnessSig(active[0], active[1], active[2] - active[1], not active[3]))

    return sorted(out)


class WitnessSigMap:
    def __init__(self, signals=[]):
        self.signals = []

        self.id_to_bit = []
        self.bit_to_id = {}
        self.bit_to_sig = {}

        for sig in signals:
            self.add_signal(sig)

    def add_signal(self, sig):
        self.signals.append(sig)
        for bit in sig.bits():
            self.add_bit(bit)
            self.bit_to_sig[bit] = sig

    def add_bit(self, bit, id=None):
        if id is None:
            id = len(self.id_to_bit)
            self.id_to_bit.append(bit)
        else:
            if len(self.id_to_bit) <= id:
                self.id_to_bit += [None] * (id - len(self.id_to_bit) + 1)
            self.id_to_bit[id] = bit
        self.bit_to_id[bit] = id


class WitnessValues:
    def __init__(self):
        self.values = {}

    def __setitem__(self, key, value):
        if isinstance(key, tuple) and len(key) == 2:
            if value != "?":
                assert isinstance(value, str)
                assert len(value) == 1
                self.values[key] = value
        else:
            assert isinstance(key, WitnessSig)
            assert key.width == len(value)
            if isinstance(value, str):
                value = reversed(value)
            for bit, bit_value in zip(key.bits(), value):
                if bit_value != "?":
                    self.values[bit] = bit_value

    def __getitem__(self, key):
        if isinstance(key, tuple) and len(key) == 2:
            return self.values.get(key, "?")
        else:
            assert isinstance(key, WitnessSig)
            return "".join([self.values.get(bit, "?") for bit in key.rev_bits()])

    def pack_present(self, sigmap):
        missing = []

        max_id = max((sigmap.bit_to_id.get(bit, -1) for bit in self.values), default=-1)

        vector = ["?"] * (max_id + 1)
        for bit, bit_value in self.values.items():
            id = sigmap.bit_to_id.get(bit, - 1)
            if id < 0:
                missing.append(bit)
            else:
                vector[max_id - sigmap.bit_to_id[bit]] = bit_value

        return "".join(vector), missing

    def pack(self, sigmap):
        packed, missing = self.pack_present(sigmap)
        if missing:
            raise RuntimeError(f"Cannot pack bits {missing!r}")
        return packed

    def unpack(self, sigmap, bits):
        for i, bit_value in enumerate(reversed(bits)):
            if bit_value != "?":
                self.values[sigmap.id_to_bit[i]] = bit_value

    def present_signals(self, sigmap):
        signals = set(sigmap.bit_to_sig.get(bit) for bit in self.values)
        missing_signals = None in signals
        if missing_signals:
            signals.discard(None)

        return sorted(signals), missing_signals


class WriteWitness:
    def __init__(self, f, generator):
        self.out = PrettyJson(f)
        self.t = 0
        self.header_written = False
        self.clocks = []
        self.signals = []

        self.out.begin_object()
        self.out.entry("format", "Yosys Witness Trace")
        self.out.entry("generator", generator)

    def add_clock(self, path, offset, edge):
        assert not self.header_written
        self.clocks.append({
            "path": path,
            "edge": edge,
            "offset": offset,
        })

    def add_sig(self, path, offset, width=1, init_only=False):
        assert not self.header_written
        sig = WitnessSig(path, offset, width, init_only)
        self.signals.append(sig)
        return sig

    def write_header(self):
        assert not self.header_written
        self.header_written = True
        self.out.name("clocks")
        self.out.array(self.clocks)

        self.signals = coalesce_signals(self.signals)
        self.sigmap = WitnessSigMap(self.signals)

        self.out.name("signals")
        self.out.array({
            "path": sig.path,
            "width": sig.width,
            "offset": sig.offset,
            "init_only": sig.init_only,
        } for sig in self.signals)

        self.out.name("steps")
        self.out.begin_array()

    def step(self, values):
        if not self.header_written:
            self.write_header()

        self.out.value({"bits": values.pack(self.sigmap)})

        self.t += 1

    def end_trace(self):
        if not self.header_written:
            self.write_header()
        self.out.end_array()
        self.out.end_object()


class ReadWitness:
    def __init__(self, f):
        data = json.load(f)
        if not isinstance(data, dict):
            data = {}

        data_format = data.get("format", "Unknown Format")

        if data_format != "Yosys Witness Trace":
            raise ValueError(f"unsupported format {data_format!r}")

        self.clocks = data["clocks"]
        for clock in self.clocks:
            clock["path"] = tuple(clock["path"])

        self.signals = [
            WitnessSig(sig["path"], sig["offset"], sig["width"], sig["init_only"])
            for sig in data["signals"]
        ]

        self.sigmap = WitnessSigMap(self.signals)

        self.bits = [step["bits"] for step in data["steps"]]

    def step(self, t):
        values = WitnessValues()
        values.unpack(self.sigmap, self.bits[t])
        return values

    def steps(self):
        for i in range(len(self.bits)):
            yield i, self.step(i)

    def __len__(self):
        return len(self.bits)
