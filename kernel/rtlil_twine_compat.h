#ifndef RTLIL_TWINE_COMPAT_H
#define RTLIL_TWINE_COMPAT_H

namespace RTLIL {

template<typename Derived> struct WrappedIdBase;
struct NameSlot;
struct CellTypeSlot;
template<typename Owner, typename Slot = NameSlot> struct OwnedId;
struct PooledName;

using ModuleNameId = OwnedId<Module>;
using WireNameId = OwnedId<Wire>;
using CellNameId = OwnedId<Cell>;
using MemoryNameId = OwnedId<Memory>;
using ProcessNameId = OwnedId<Process>;
using CellTypeId = OwnedId<Cell, CellTypeSlot>;

namespace wrapped_idstring_detail {

inline std::string render_escaped(const TwinePool *pool, IdString id) {
	if (id == IdString::Null)
		return std::string();
	return pool ? pool->str(id) : ID::str(id);
}

inline std::string render_unescaped(const TwinePool *pool, IdString id) {
	if (id == IdString::Null)
		return std::string();
	return pool ? pool->unescaped_str(id) : ID::unescaped_str(id);
}

}

template<typename Derived>
struct WrappedIdBase {
	operator IdString() const { return self().ref(); }
	operator std::string() const { return self().escaped(); }
	std::string escaped() const { return wrapped_idstring_detail::render_escaped(self().pool(), self().ref()); }
	std::string unescape() const { return wrapped_idstring_detail::render_unescaped(self().pool(), self().ref()); }
	bool isPublic() const { return self().ref().isPublic(); }
	bool empty() const { return self().ref() == IdString::Null; }
	std::string str() const { return self().escaped(); }
	bool begins_with(const char *s) const {
		const TwinePool *pool = self().pool();
		return pool ? pool->begins_with(self().ref(), s) : str().starts_with(s);
	}
	bool ends_with(const char *s) const { return str().ends_with(s); }
	template<typename... Ts> bool in(Ts &&...args) const {
		return self().ref().in(std::forward<Ts>(args)...);
	}
	bool in(const pool<IdString> &rhs) const { return self().ref().in(rhs); }
	std::string substr(size_t pos = 0, size_t len = std::string::npos) const {
		return self().escaped().substr(pos, len);
	}
	size_t size() const {
		const TwinePool *pool = self().pool();
		return pool ? pool->str_size(self().ref()) : self().escaped().size();
	}
	bool contains(const char *p) const { return self().escaped().find(p) != std::string::npos; }
	char operator[](int n) const { return self().escaped()[n]; }
	bool lt_by_name(const Derived &rhs) const {
		const TwinePool *pool = self().pool();
		if (pool == nullptr)
			return self().escaped() < rhs.escaped();
		return pool->compare_by_name(self().ref(), rhs.ref()) < 0;
	}
	friend bool operator==(const Derived &lhs, const Derived &rhs) { return lhs.ref() == rhs.ref(); }
	friend bool operator==(const Derived &lhs, IdString rhs) { return lhs.ref() == rhs; }
	friend bool operator==(const Derived &lhs, NullIdString) { return lhs.ref() == IdString::Null; }
	friend bool operator==(const Derived &lhs, const std::string &rhs) {
		const TwinePool *pool = lhs.pool();
		return pool ? pool->name_equal(lhs.ref(), rhs) : lhs.escaped() == rhs;
	}
	friend bool operator<(const Derived &lhs, const Derived &rhs) { return lhs.ref() < rhs.ref(); }
private:
	const Derived &self() const { return *static_cast<const Derived *>(this); }
};

template<typename T>
concept IsWrappedId = std::is_base_of_v<WrappedIdBase<std::decay_t<T>>, std::decay_t<T>>;

// Two wrapped IdStrings can be compared for equality by comparing .ref()
template<IsWrappedId A, IsWrappedId B>
requires (!std::is_same_v<A, B>)
inline bool operator==(const A &lhs, const B &rhs) { return lhs.ref() == rhs.ref(); }

// A pair can be created from wrapped IdStrings by unwrapping them to IdString
// otherwise, you'd try to copy an OwnedId into the arguments of std::make_pair
// which would error out as its copy constructor is deleted
template<IsWrappedId A, typename B>
auto make_pair(A &&a, B &&b) { return std::make_pair(a.ref(), std::forward<B>(b)); }
template<typename A, IsWrappedId B>
auto make_pair(A &&a, B &&b) { return std::make_pair(std::forward<A>(a), b.ref()); }
template<IsWrappedId A, IsWrappedId B>
auto make_pair(A &&a, B &&b) { return std::make_pair(a.ref(), b.ref()); }

template<typename Owner, typename Slot>
struct OwnedId : WrappedIdBase<OwnedId<Owner, Slot>> {
	OwnedId() = default;
	OwnedId(const OwnedId &) = delete;
	OwnedId(OwnedId &&) = delete;
	IdString ref() const { return id_; }
	const TwinePool *pool() const;
	OwnedId &operator=(IdString id) { id_ = id; return *this; }
	OwnedId &operator=(const OwnedId &other) { return *this = other.ref(); }
	OwnedId &operator=(OwnedId &&other) { return *this = other.ref(); }
	friend void swap(OwnedId &a, OwnedId &b) { std::swap(a.id_, b.id_); }
private:
	const Owner *owner() const;
	IdString id_;
};

struct PooledName : WrappedIdBase<PooledName> {
	PooledName() = default;
	explicit PooledName(IdString id) : id_(id) {}
	PooledName(const TwinePool *pool, IdString id) : pool_(pool), id_(id) {}
	PooledName(const Design *design, IdString id);
	PooledName(const Module *module, IdString id);
	template<typename D> PooledName(const WrappedIdBase<D> &masq)
		: pool_(static_cast<const D &>(masq).pool()),
		  id_(static_cast<const D &>(masq).ref()) {}
	IdString ref() const { return id_; }
	const TwinePool *pool() const { return pool_; }
private:
	const TwinePool *pool_ = nullptr;
	IdString id_;
};

}

namespace hashlib {
	template<typename T>
	struct masq_hash_ops {
		static inline bool cmp(const T &a, const T &b) { return a == b; }
		[[nodiscard]] static inline Hasher hash(const T &a) {
			return hash_ops<IdString>::hash(a.ref());
		}
		[[nodiscard]] static inline Hasher hash_into(const T &a, Hasher h) {
			return hash_ops<IdString>::hash_into(a.ref(), h);
		}
	};

	template<typename Owner, typename Slot>
	struct hash_ops<RTLIL::OwnedId<Owner, Slot>> : masq_hash_ops<RTLIL::OwnedId<Owner, Slot>> {};
	template<> struct hash_ops<RTLIL::PooledName> : masq_hash_ops<RTLIL::PooledName> {};
}

#endif
