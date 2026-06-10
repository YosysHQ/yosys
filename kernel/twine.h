#ifndef YOSYS_TWINE_H
#define YOSYS_TWINE_H

#include "kernel/yosys_common.h"
#include "kernel/hashlib.h"

#include "libs/plf_colony/plf_colony.h"
#include <cstdint>
#include <limits>
#include <span>
#include <sstream>
#include <string>
#include <string_view>
#include <unordered_set>
#include <list>
#include <variant>
#include <vector>

YOSYS_NAMESPACE_BEGIN

struct Twine;
struct TwinePool;

using TwineRef = size_t;

enum : short {
	STATIC_TWINE_BEGIN = 0,
#define X(N) IDX_##N,
#include "kernel/constids.inc"
#undef X
	STATIC_TWINE_END
};

struct TW {
#define X(N) static constexpr TwineRef N = IDX_##N;
#include "kernel/constids.inc"
#undef X
};

struct Twine {
	static constexpr TwineRef Null = std::numeric_limits<size_t>::max();

	struct Suffix {
		TwineRef prefix;
		std::string tail;
		// TODO check
		auto operator<=>(const Suffix&) const = default;
	};

	std::variant<std::monostate, std::string, std::vector<TwineRef>, Suffix> data;

	bool is_dead() const { return std::holds_alternative<std::monostate>(data); }
	bool is_leaf() const { return std::holds_alternative<std::string>(data); }
	bool is_concat() const { return std::holds_alternative<std::vector<TwineRef>>(data); }
	bool is_suffix() const { return std::holds_alternative<Suffix>(data); }
	bool is_flat() const { return is_leaf() || is_suffix(); }
	const std::string &leaf() const { return std::get<std::string>(data); }
	const std::vector<TwineRef> &children() const { return std::get<std::vector<TwineRef>>(data); }
	const Suffix &suffix() const { return std::get<Suffix>(data); }
};

struct TwineHash {
	using is_transparent = void;

	const TwinePool* pool = nullptr;

	size_t operator()(const Twine& t) const noexcept;
	size_t operator()(TwineRef ref) const noexcept;
	// size_t operator()(std::string_view v) const noexcept;
};

struct TwineEq {
	using is_transparent = void;

	const TwinePool* pool = nullptr;

	bool operator()(TwineRef a, TwineRef b) const noexcept;
	bool operator()(TwineRef a, const Twine& b) const noexcept;
	bool operator()(const Twine& a, TwineRef b) const noexcept;
	// bool operator()(TwineRef a, std::string_view b) const noexcept;
	// bool operator()(std::string_view a, TwineRef b) const noexcept;
};


TwineRef twine_populate(std::string name);
void twine_prepopulate();

struct TwinePool {
	static std::vector<Twine> globals_;
	plf::colony<Twine> backing;
	std::unordered_set<TwineRef, TwineHash, TwineEq> index;

	const Twine& operator[] (TwineRef ref) const {
		if (ref < STATIC_TWINE_END)
			return globals_[ref];
		else
			return backing[ref - STATIC_TWINE_END];
	}

	void dump(TwineRef ref, std::ostream& os = std::cout) const {
		const Twine& twine = (*this)[ref];
		std::visit([&](const auto& val) {
			using T = std::decay_t<decltype(val)>;
			if constexpr (std::is_same_v<T, std::monostate>) {
				os << "Dead()";
			} else if constexpr (std::is_same_v<T, std::string>) {
				os << "Leaf(\"" << val << "\")";
			} else if constexpr (std::is_same_v<T, std::vector<TwineRef>>) {
				os << "Concat[";
				for (size_t i = 0; i < val.size(); ++i) {
					if (i > 0)
						os << ", ";
					dump(val[i], os);
				}
				os << "]";
			} else if constexpr (std::is_same_v<T, Twine::Suffix>) {
				os << "Suffix(prefix: ";
				dump(val.prefix, os);
				os << ", tail: \"" << val.tail << "\")";
			}
		}, twine.data);
	}
	void print(TwineRef ref, std::ostream& os = std::cout) const {
		std::visit([&](const auto& val) {
			using T = std::decay_t<decltype(val)>;
			if constexpr (std::is_same_v<T, std::monostate>) {
			} else if constexpr (std::is_same_v<T, std::string>) {
				os << val;
			} else if constexpr (std::is_same_v<T, std::vector<TwineRef>>) {
				for (size_t i = 0; i < val.size(); ++i) {
					if (i > 0)
						os << "|";
					print(val[i], os);
				}
			} else if constexpr (std::is_same_v<T, Twine::Suffix>) {
				print(val.prefix, os);
				os << val.tail;
			}
		}, (*this)[ref].data);
	}
	std::string str(TwineRef ref) const {
		std::ostringstream os;
		print(ref, os);
		return os.str();
	}

	TwinePool() : index(0, TwineHash{this}, TwineEq{this}) {
		rebuild_index();
	}
	TwinePool(const TwinePool& other) : backing(other.backing), index(0, TwineHash{this}, TwineEq{this}) {
		rebuild_index();
	}
	TwinePool(TwinePool&& other) : backing(std::move(other.backing)), index(0, TwineHash{this}, TwineEq{this}) {
		rebuild_index();
	}
	TwinePool& operator=(const TwinePool& other) {
		if (this != &other) {
			backing = other.backing;
			index = std::unordered_set<TwineRef, TwineHash, TwineEq>(0, TwineHash{this}, TwineEq{this});
			rebuild_index();
		}
		return *this;
	}
	TwinePool& operator=(TwinePool&& other) {
		if (this != &other) {
			backing = std::move(other.backing);
			index = std::unordered_set<TwineRef, TwineHash, TwineEq>(0, TwineHash{this}, TwineEq{this});
			rebuild_index();
		}
		return *this;
	}

	void rebuild_index() {
		for (TwineRef ref = 0; ref < globals_.size(); ref++)
			index.insert(ref);
		for (auto it = backing.begin(); it != backing.end(); ++it)
			index.insert(STATIC_TWINE_END + backing.get_index(it));
	}

	TwineRef find(const Twine& t) const {
		if (auto it = index.find(t); it != index.end()) {
			return *it;
		}
		return Twine::Null;
	}

	TwineRef add(Twine t) {
		if (auto it = index.find(t); it != index.end()) {
			return *it;
		}

		auto colony_it = backing.insert(std::move(t));
		TwineRef ref = STATIC_TWINE_END + backing.get_index(colony_it);
		index.insert(ref);
		return ref;
	}

	void dump(std::ostream& os = std::cout) const {
		os << "--- TwinePool Dump (" << backing.size() << " nodes) ---\n";
		for (auto it = backing.begin(); it != backing.end(); ++it) {
			TwineRef ref = STATIC_TWINE_END + backing.get_index(it);
			os << ref << " -> ";
			dump(ref, os);
			os << '\n';
		}
		os << "--------------------------------\n";
	}
	// Silly compat
	std::string flat_string(TwineRef t) const { return str(t); }
};

inline size_t TwineHash::operator()(const Twine& t) const noexcept {
	// size_t h = std::hash<size_t>{}(t.data.index());
	Hasher h;

	std::visit([&h](const auto& val) {
		using T = std::decay_t<decltype(val)>;

		// auto combine = [&h](auto v) {
		// 	h ^= v + 0x9e3779b9 + (h << 6) + (h >> 2);
		// };

		if constexpr (std::is_same_v<T, std::string>) {
			h.eat(val);
			// combine(std::hash<std::string>{}(val));
		} else if constexpr (std::is_same_v<T, std::vector<TwineRef>>) {
			for (auto ref : val) {
				h.eat(ref);
				// combine(std::hash<TwineRef>{}(ref));
			}
		} else if constexpr (std::is_same_v<T, Twine::Suffix>) {
			h.eat(val.prefix);
			h.eat(val.tail);
			// combine(std::hash<TwineRef>{}(val.prefix));
			// combine(std::hash<std::string>{}(val.tail));
		}
	}, t.data);

	return h.yield();
}

inline size_t TwineHash::operator()(TwineRef ref) const noexcept {
	return (*this)((*pool)[ref]);
}

inline bool TwineEq::operator()(TwineRef a, TwineRef b) const noexcept {
	return (*pool)[a].data == (*pool)[b].data;
}

inline bool TwineEq::operator()(TwineRef a, const Twine& b) const noexcept {
	return (*pool)[a].data == b.data;
}

inline bool TwineEq::operator()(const Twine& a, TwineRef b) const noexcept {
	return a.data == (*pool)[b].data;
}


struct DeepTwineHash {
	using is_transparent = void;

	const TwinePool* pool = nullptr;

	// FNV-1a constants for 64-bit
	static constexpr size_t FNV_OFFSET_BASIS = 14695981039346656037ull;
	static constexpr size_t FNV_PRIME = 1099511628211ull;

	static void combine(size_t& hash, std::string_view sv) noexcept {
		for (char c : sv) {
			hash ^= static_cast<size_t>(c);
			hash *= FNV_PRIME;
		}
	}

	// Recursively hash the fragments of a Twine
	void combine(size_t& hash, TwineRef t) const noexcept {
		if (t == Twine::Null)
			return;
		const Twine& n = (*pool)[t];
		if (n.is_dead()) return;

		if (n.is_leaf()) {
			combine(hash, std::string_view(n.leaf()));
		} else if (n.is_concat()) {
			for (auto child : n.children()) combine(hash, child);
		} else if (n.is_suffix()) {
			combine(hash, n.suffix().prefix);
			combine(hash, std::string_view(n.suffix().tail));
		}
	}

	size_t operator()(std::string_view sv) const noexcept {
		size_t h = FNV_OFFSET_BASIS;
		combine(h, sv);
		return h;
	}

	size_t operator()(TwineRef t) const noexcept {
		size_t h = FNV_OFFSET_BASIS;
		combine(h, t);
		return h;
	}
};

struct DeepTwineEq {
	using is_transparent = void;

	const TwinePool* pool = nullptr;

	// Recursively consumes the string_view to check for deep equality
	bool consume(TwineRef t, std::string_view& sv) const noexcept {
		if (t == Twine::Null)
			return true;
		const Twine& n = (*pool)[t];
		if (n.is_dead()) return true;

		if (n.is_leaf()) {
			if (!sv.starts_with(n.leaf())) return false;
			sv.remove_prefix(n.leaf().size());
			return true;
		} else if (n.is_concat()) {
			for (auto child : n.children()) {
				if (!consume(child, sv)) return false;
			}
			return true;
		} else if (n.is_suffix()) {
			if (!consume(n.suffix().prefix, sv)) return false;
			if (!sv.starts_with(n.suffix().tail)) return false;
			sv.remove_prefix(n.suffix().tail.size());
			return true;
		}
		return false;
	}

	bool operator()(TwineRef t, std::string_view sv) const noexcept {
		return consume(t, sv) && sv.empty();
	}

	bool operator()(std::string_view sv, TwineRef t) const noexcept {
		return (*this)(t, sv);
	}

	// Required by unordered_set to handle hash collisions between two TwineRefs.
	bool operator()(TwineRef a, TwineRef b) const {
		if (a == b) return true; // Index or structural equality shortcut
		std::string fb = flatten(b);
		return (*this)(a, std::string_view(fb));
	}

	// Helper to flatten a twine (used only during rare hash collisions)
	std::string flatten(TwineRef t) const {
		std::string result;
		auto append = [&](auto& self, TwineRef ref) -> void {
			if (ref == Twine::Null)
				return;
			const Twine& node = (*pool)[ref];
			if (node.is_dead()) return;
			if (node.is_leaf()) result += node.leaf();
			else if (node.is_concat()) {
				for (auto child : node.children()) self(self, child);
			} else if (node.is_suffix()) {
				self(self, node.suffix().prefix);
				result += node.suffix().tail;
			}
		};
		append(append, t);
		return result;
	}
};

struct TwineSearch {
	TwinePool* pool;
	std::unordered_set<TwineRef, DeepTwineHash, DeepTwineEq> index;
	TwineSearch(TwinePool* pool) : pool(pool), index(0, DeepTwineHash{pool}, DeepTwineEq{pool}) {
		for (auto it = pool->backing.begin(); it != pool->backing.end(); ++it) {
			index.insert(STATIC_TWINE_END + pool->backing.get_index(it));
		}
	}
	TwineRef find(std::string_view sv) const {
		if (auto it = index.find(sv); it != index.end()) {
			return *it;
		}
		return Twine::Null;
	}
};

// struct TwinePoolExtender {
// 	TwinePool& pool;
// 	size_t offset;
// private:
// 	size_t resize_for_idx(size_t idx) {
// 		auto real_idx = offset + idx;
// 		pool.nodes_.resize(std::max(pool.nodes_.size(), real_idx + 1));
// 		return real_idx;
// 	}
// 	void commit(Twine&& twine, size_t idx) {
// 		pool.nodes_[idx] = std::move(twine);
// 		pool.leaf_index_.insert(&pool.nodes_[idx]);
// 	}
// public:
// 	// TwinePoolExtender(Design* design) : pool(design->twines), offset(design->twines.size()) {}
// 	void extend_leaf(std::string leaf, size_t idx) {
// 		auto real_idx = resize_for_idx(idx);
// 		commit(Twine(leaf), real_idx);
// 	}
// 	void extend_concat(std::vector<size_t> children, size_t idx) {
// 		auto real_idx = resize_for_idx(idx);
// 		Twine* first = &pool.nodes_.front() + offset;
// 		std::vector<Twine*> real_children;
// 		real_children.reserve(children.size());
// 		for (auto child : children)
// 			real_children.push_back(first + child);
// 		commit(Twine(std::move(real_children)), real_idx);
// 	}
// 	void extend_suffix(size_t prefix, std::string tail, size_t idx) {
// 		auto real_idx = resize_for_idx(idx);
// 		Twine* first = &pool.nodes_.front() + offset;
// 		Twine* real_prefix = first + prefix;
// 		commit(Twine(Twine::Suffix(real_prefix, std::move(tail))), real_idx);
// 	}
// 	void finish() {
// 		for (size_t i = offset; i < pool.nodes_.size(); i++)
// 			if (pool.nodes_[i].is_dead())
// 				pool.free_list_.push_back(&pool.nodes_[i]);
// 	}
// };

YOSYS_NAMESPACE_END

#endif
