#ifndef RTLIL_TWINE_COMPAT_H
#define RTLIL_TWINE_COMPAT_H

namespace RTLIL {

template<typename Derived> struct IdMasqBase;
template<typename Owner, auto Field = &NamedObject::name_> struct IdFieldMasq;
struct PooledName;

using ModuleNameMasq = IdFieldMasq<Module>;
using WireNameMasq = IdFieldMasq<Wire>;
using CellNameMasq = IdFieldMasq<Cell>;
using MemoryNameMasq = IdFieldMasq<Memory>;
using ProcessNameMasq = IdFieldMasq<Process>;

namespace masq_detail {

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
struct IdMasqBase {
	operator IdString() const { return self().ref(); }
	operator std::string() const { return self().escaped(); }
	std::string escaped() const { return masq_detail::render_escaped(self().pool(), self().ref()); }
	std::string unescape() const { return masq_detail::render_unescaped(self().pool(), self().ref()); }
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
concept IsIdMasq = std::is_base_of_v<IdMasqBase<std::decay_t<T>>, std::decay_t<T>>;

// Two masq can be compared for equality by comparing .ref()
template<IsIdMasq A, IsIdMasq B>
requires (!std::is_same_v<A, B>)
inline bool operator==(const A &lhs, const B &rhs) { return lhs.ref() == rhs.ref(); }

// A pair can be created from two masqs
// otherwise, you'd try to construct masqs in the arguments of std::make_pair
// which would error out as the constructor is deleted
template<IsIdMasq A, typename B>
auto make_pair(A &&a, B &&b) { return std::make_pair(a.ref(), std::forward<B>(b)); }
template<typename A, IsIdMasq B>
auto make_pair(A &&a, B &&b) { return std::make_pair(std::forward<A>(a), b.ref()); }
template<IsIdMasq A, IsIdMasq B>
auto make_pair(A &&a, B &&b) { return std::make_pair(a.ref(), b.ref()); }

template<typename Owner, auto Field>
struct IdFieldMasq : IdMasqBase<IdFieldMasq<Owner, Field>> {
	IdFieldMasq() = default;
	IdFieldMasq(const IdFieldMasq &) = delete;
	IdFieldMasq(IdFieldMasq &&) = delete;
	IdString ref() const { return owner()->*Field; }
	const TwinePool *pool() const;
	IdFieldMasq &operator=(IdString id) { owner()->*Field = id; return *this; }
	IdFieldMasq &operator=(const IdFieldMasq &other) { return *this = other.ref(); }
	IdFieldMasq &operator=(IdFieldMasq &&other) { return *this = other.ref(); }
private:
	const Owner *owner() const;
	Owner *owner() { return const_cast<Owner *>(static_cast<const IdFieldMasq *>(this)->owner()); }
};

Module *module_by_name(Design *design, const std::string &name);
Wire *wire_by_name(Module *module, const std::string &name);
pool<std::string> object_names(const Module *module);

struct PooledName : IdMasqBase<PooledName> {
	PooledName() = default;
	explicit PooledName(IdString id) : id_(id) {}
	PooledName(const TwinePool *pool, IdString id) : pool_(pool), id_(id) {}
	PooledName(const Design *design, IdString id);
	PooledName(const Module *module, IdString id);
	template<typename D> PooledName(const IdMasqBase<D> &masq)
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

	template<typename Owner, auto Field>
	struct hash_ops<RTLIL::IdFieldMasq<Owner, Field>> : masq_hash_ops<RTLIL::IdFieldMasq<Owner, Field>> {};
	template<> struct hash_ops<RTLIL::PooledName> : masq_hash_ops<RTLIL::PooledName> {};
}

#endif
