#ifndef RTLIL_TWINE_COMPAT_IMPL_H
#define RTLIL_TWINE_COMPAT_IMPL_H

#ifdef __GNUC__
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Winvalid-offsetof"
#endif

namespace RTLIL {

template<typename Owner, auto Field>
inline const Owner *IdFieldMasq<Owner, Field>::owner() const {
	size_t offset;
	if constexpr (std::is_same_v<decltype(Field), IdString NamedObject::*>) {
		static_assert(Field == &NamedObject::name_);
		offset = offsetof(Owner, name);
	} else {
		static_assert(std::is_same_v<Owner, Cell> && std::is_same_v<decltype(Field), IdString Cell::*>);
		if constexpr (std::is_same_v<decltype(Field), IdString Cell::*>)
			static_assert(Field == &Cell::type_impl);
		offset = offsetof(Cell, type);
	}
	return reinterpret_cast<const Owner *>(reinterpret_cast<const char *>(this) - offset);
}

template<typename Owner, auto Field>
inline const TwinePool *IdFieldMasq<Owner, Field>::pool() const {
	const Owner *o = owner();
	if constexpr (std::is_same_v<Owner, Module>) {
		return o->design ? &o->design->twines : nullptr;
	} else {
		static_assert(std::is_same_v<Owner, Wire> || std::is_same_v<Owner, Cell>
				|| std::is_same_v<Owner, Memory> || std::is_same_v<Owner, Process>);
		return o->module && o->module->design ? &o->module->design->twines : nullptr;
	}
}

inline PooledName::PooledName(const Design *design, IdString id)
	: pool_(design ? &design->twines : nullptr), id_(id) { }

inline PooledName::PooledName(const Module *module, IdString id)
	: PooledName(module ? module->design : nullptr, id) { }

}

#ifdef __GNUC__
#pragma GCC diagnostic pop
#endif

template<typename Derived>
inline void log_dump_val_worker(const RTLIL::IdMasqBase<Derived> &name) {
	log("%s", static_cast<const Derived &>(name).unescape());
}

#endif
