#ifndef YOSYS_TWINE_H
#define YOSYS_TWINE_H

#include "kernel/yosys_common.h"
#include "kernel/hashlib.h"

#include "libs/plf_colony/plf_colony.h"
#include <cstdint>
#include <limits>
#include <span>
#include <string>
#include <string_view>
#include <unordered_set>
#include <list>
#include <variant>
#include <vector>

YOSYS_NAMESPACE_BEGIN

struct Twine;
struct TwineRef {
	std::variant<Twine*, size_t> data;
	constexpr TwineRef(Twine* p) : data(p) {}
	constexpr TwineRef(size_t global) : data(global) {}
	const Twine& operator*() const;
	Twine& operator*();
	Twine* operator->() {
		return &(**this);
	}
	const Twine* operator->() const {
		return &(**this);
	}
	friend constexpr bool operator==(const TwineRef& a, const TwineRef& b) {
		return &*a == &*b;
	}
	friend constexpr auto operator<=>(const TwineRef& a, const TwineRef& b) {
		return &*a <=> &*b;
	}
};
// using TwineRef = const Twine*;

struct Twine {
	static constexpr TwineRef Null = nullptr;

	struct Suffix {
		TwineRef prefix;
		std::string tail;
		// TODO check
		// auto operator<=>(const Suffix&) const = default;
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
	void dump(std::ostream& os = std::cout) const {
		std::visit([&os](const auto& val) {
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
					val[i]->dump(os);
				}
				os << "]";
			} else if constexpr (std::is_same_v<T, Suffix>) {
				os << "Suffix(prefix: ";
				val.prefix->dump(os);
				os << ", tail: \"" << val.tail << "\")";
			}
		}, data);
	}
	void print(std::ostream& os = std::cout) const {
		std::visit([&os](const auto& val) {
			using T = std::decay_t<decltype(val)>;
			if constexpr (std::is_same_v<T, std::monostate>) {
			} else if constexpr (std::is_same_v<T, std::string>) {
				os << val;
			} else if constexpr (std::is_same_v<T, std::vector<TwineRef>>) {
				for (size_t i = 0; i < val.size(); ++i) {
					if (i > 0)
						os << "|";
					val[i]->print(os);
				}
			} else if constexpr (std::is_same_v<T, Suffix>) {
				val.prefix->print(os);
				os << val.tail;
			}
		}, data);
	}
	std::string str() const {
		std::string str;
		std::stringstream os(str);
		print(os);
		return str;
	}
};

struct TwineHash {
	using is_transparent = void;

	size_t operator()(const Twine& t) const noexcept;
	size_t operator()(TwineRef ptr) const noexcept;
	// size_t operator()(std::string_view v) const noexcept;
};

struct TwineEq {
	using is_transparent = void;

	bool operator()(TwineRef a, TwineRef b) const noexcept;
	bool operator()(TwineRef a, const Twine& b) const noexcept;
	bool operator()(const Twine& a, TwineRef b) const noexcept;
	// bool operator()(TwineRef a, std::string_view b) const noexcept;
	// bool operator()(std::string_view a, TwineRef b) const noexcept;
};

struct TwinePool {
	static std::vector<Twine> globals_;
	plf::colony<Twine> backing;
	std::unordered_set<TwineRef, TwineHash, TwineEq> index;

	TwinePool() {
		for (Twine& t : globals_)
			index.insert(&t);
	}

	TwineRef find(Twine t) const {
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
		TwineRef ptr = &(*colony_it);
		index.insert(ptr);
		return ptr;
	}

	void dump(std::ostream& os = std::cout) const {
		os << "--- TwinePool Dump (" << backing.size() << " nodes) ---\n";
		for (const auto& t : backing) {
			os << static_cast<const void*>(&t) << " -> ";
			t.dump(os);
			os << '\n';
		}
		os << "--------------------------------\n";
	}
	// Silly compat
	std::string flat_string(TwineRef t) const { return t->str(); }
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

inline size_t TwineHash::operator()(TwineRef ptr) const noexcept {
	return (*this)(*ptr);
}

inline bool TwineEq::operator()(TwineRef a, TwineRef b) const noexcept {
	return a->data == b->data;
}

inline bool TwineEq::operator()(TwineRef a, const Twine& b) const noexcept {
	return a->data == b.data;
}

inline bool TwineEq::operator()(const Twine& a, TwineRef b) const noexcept {
	return a.data == b->data;
}


struct DeepTwineHash {
	using is_transparent = void;

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
	static void combine(size_t& hash, TwineRef t) noexcept {
		if (!t || t->is_dead()) return;

		if (t->is_leaf()) {
			combine(hash, t->leaf());
		} else if (t->is_concat()) {
			for (auto child : t->children()) combine(hash, child);
		} else if (t->is_suffix()) {
			combine(hash, t->suffix().prefix);
			combine(hash, t->suffix().tail);
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

	// Recursively consumes the string_view to check for deep equality
	static bool consume(TwineRef t, std::string_view& sv) noexcept {
		if (!t || t->is_dead()) return true;

		if (t->is_leaf()) {
			if (!sv.starts_with(t->leaf())) return false;
			sv.remove_prefix(t->leaf().size());
			return true;
		} else if (t->is_concat()) {
			for (auto child : t->children()) {
				if (!consume(child, sv)) return false;
			}
			return true;
		} else if (t->is_suffix()) {
			if (!consume(t->suffix().prefix, sv)) return false;
			if (!sv.starts_with(t->suffix().tail)) return false;
			sv.remove_prefix(t->suffix().tail.size());
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
		if (a == b) return true; // Pointer or structural equality shortcut
		return (*this)(a, flatten(b));
	}

	// Helper to flatten a twine (used only during rare hash collisions)
	static std::string flatten(TwineRef t) {
		std::string result;
		auto append = [&result](auto& self, TwineRef node) -> void {
			if (!node || node->is_dead()) return;
			if (node->is_leaf()) result += node->leaf();
			else if (node->is_concat()) {
				for (auto child : node->children()) self(self, child);
			} else if (node->is_suffix()) {
				self(self, node->suffix().prefix);
				result += node->suffix().tail;
			}
		};
		append(append, t);
		return result;
	}
};

struct TwineSearch {
	std::unordered_set<TwineRef, DeepTwineHash, DeepTwineEq> index;
	TwinePool* pool;
	TwineSearch(TwinePool* pool) : pool(pool) {
		for (auto& t : pool->backing) {
			index.insert(&t);
		}
	}
	TwineRef find(std::string_view sv) const {
		if (auto it = index.find(sv); it != index.end()) {
			return *it;
		}
		return Twine::Null;
	}
};

// enum : short {
// 	STATIC_ID_BEGIN = 0,
// #define X(N) IDX_##N,
// #include "kernel/constids.inc"
// #undef X
// 	STATIC_ID_END
// };


class TW
{
public:
	constexpr explicit TW(short v) : internal(v) {}

	constexpr operator TwineRef() const
	{
		return &TwinePool::globals_[internal];
	}

#define X(N) static const TW N;
#include "kernel/constids.inc"
#undef X

private:
	short internal;
};

Twine& TwineRef::operator*() {
	// Ugly
	std::visit([](const auto& data) {
		using T = std::decay_t<decltype(data)>;
		if constexpr (std::is_same_v<Twine*, std::monostate>) {
			return *data;
		} else {
			return TwinePool::globals_[data];
		}
	}, data);
}

const Twine& TwineRef::operator*() const {
	// Ugly
	std::visit([](const auto& data) {
		using T = std::decay_t<decltype(data)>;
		if constexpr (std::is_same_v<Twine*, std::monostate>) {
			return *data;
		} else {
			return TwinePool::globals_[data];
		}
	}, data);
}

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
