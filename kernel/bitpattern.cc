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

#include "kernel/bitpattern.h"

YOSYS_NAMESPACE_BEGIN

BitPatternPool::BitPatternPool(RTLIL::SigSpec sig) : width(GetSize(sig))
{
	gave_up = width > MAX_WIDTH;
	if (gave_up)
		return;
	universe.assign(width, RTLIL::State::Sa);
	for (int i = 0; i < width; i++)
		if (sig[i].wire == nullptr && sig[i].data <= RTLIL::State::S1)
			universe[i] = sig[i].data;
	rebuild();
}

BitPatternPool::BitPatternPool(int width) : BitPatternPool(RTLIL::SigSpec(RTLIL::State::Sa, width)) {}

bool BitPatternPool::covers_nothing(RTLIL::SigSpec sig)
{
	for (auto bit : sig)
		if (bit.wire == nullptr && (bit.data == RTLIL::State::Sx || bit.data == RTLIL::State::Sz))
			return true;
	return false;
}

int BitPatternPool::budget() { return max_nodes >> (3 * ((MAX_ATTEMPTS - 1 - attempt) / 2)); }

int BitPatternPool::bit_index(int level) { return attempt % 2 ? level : width - 1 - level; }

int BitPatternPool::make_node(int level, int low, int high)
{
	if (low == high)
		return low;
	return nodes(std::make_tuple(level, low, high));
}

bool BitPatternPool::reaches(int node, const std::vector<RTLIL::State> &bits, int terminal, pool<int> &misses)
{
	if (node == int(Terminal::Empty) || node == int(Terminal::Full))
		return node == terminal;
	if (misses.count(node))
		return false;
	auto [level, low, high] = nodes[node];
	RTLIL::State bit = bits[bit_index(level)];
	if (bit != RTLIL::State::S1 && reaches(low, bits, terminal, misses))
		return true;
	if (bit != RTLIL::State::S0 && reaches(high, bits, terminal, misses))
		return true;
	misses.insert(node);
	return false;
}

// node minus cube
int BitPatternPool::remove_cube(int node, int level, const std::vector<RTLIL::State> &bits, dict<std::pair<int, int>, int> &cache)
{
	if (node == int(Terminal::Empty))
		return int(Terminal::Empty);
	while (level < width && bits[bit_index(level)] > RTLIL::State::S1)
		level++;
	if (level == width || GetSize(nodes) >= budget())
		return int(Terminal::Empty);
	auto it = cache.find({node, level});
	if (it != cache.end())
		return it->second;

	auto [node_level, low, high] = nodes[node];
	int result;
	if (node_level < level) {
		low = remove_cube(low, level, bits, cache);
		high = remove_cube(high, level, bits, cache);
		result = make_node(node_level, low, high);
	} else {
		if (node_level > level)
			low = high = node;
		if (bits[bit_index(level)] == RTLIL::State::S0)
			low = remove_cube(low, level + 1, bits, cache);
		else
			high = remove_cube(high, level + 1, bits, cache);
		result = make_node(level, low, high);
	}
	cache[{node, level}] = result;
	return result;
}

// false if over budget
bool BitPatternPool::remove(const std::vector<RTLIL::State> &bits)
{
	log_assert(GetSize(bits) == width);
	dict<std::pair<int, int>, int> cache;
	int new_root = remove_cube(root, 0, bits, cache);
	if (GetSize(nodes) >= budget())
		return false;
	root = new_root;
	return true;
}

bool BitPatternPool::rebuild()
{
	nodes.clear();
	nodes(std::make_tuple(width, int(Terminal::Empty), int(Terminal::Empty)));
	nodes(std::make_tuple(width, int(Terminal::Full), int(Terminal::Full)));
	root = width > 0 ? int(Terminal::Full) : int(Terminal::Empty);
	for (int level = width - 1; level >= 0; level--) {
		RTLIL::State bit = universe[bit_index(level)];
		if (bit == RTLIL::State::S1)
			root = make_node(level, int(Terminal::Empty), root);
		else if (bit == RTLIL::State::S0)
			root = make_node(level, root, int(Terminal::Empty));
	}
	for (auto &bits : taken)
		if (!remove(bits))
			return false;
	return true;
}

bool BitPatternPool::has_any(RTLIL::SigSpec sig)
{
	if (covers_nothing(sig))
		return false;
	if (gave_up)
		return true;
	log_assert(GetSize(sig) == width);
	pool<int> misses;
	return reaches(root, sig.as_const().to_bits(), int(Terminal::Full), misses);
}

bool BitPatternPool::has_all(RTLIL::SigSpec sig)
{
	if (covers_nothing(sig))
		return true;
	if (gave_up)
		return false;
	log_assert(GetSize(sig) == width);
	pool<int> misses;
	return !reaches(root, sig.as_const().to_bits(), int(Terminal::Empty), misses);
}

bool BitPatternPool::take(RTLIL::SigSpec sig)
{
	if (covers_nothing(sig))
		return false;
	if (gave_up)
		return true;
	if (root == int(Terminal::Empty))
		return false;
	std::vector<RTLIL::State> bits = sig.as_const().to_bits();
	int old_root = root;
	bool removed = remove(bits);
	while (!removed && attempt + 1 < MAX_ATTEMPTS) {
		attempt++;
		if (rebuild()) {
			old_root = root;
			removed = remove(bits);
		}
	}
	if (!removed) {
		gave_up = true;
		nodes = {};
		taken = {};
		return true;
	}
	// hash-consed, same root means no overlap
	if (root == old_root)
		return false;
	if (attempt + 1 < MAX_ATTEMPTS)
		taken.push_back(bits);
	return true;
}

bool BitPatternPool::take_all()
{
	if (empty())
		return false;
	root = int(Terminal::Empty);
	gave_up = false;
	return true;
}

bool BitPatternPool::empty() { return !gave_up && root == int(Terminal::Empty); }

YOSYS_NAMESPACE_END
