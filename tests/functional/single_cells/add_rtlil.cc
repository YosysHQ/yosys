#include <cxxrtl/cxxrtl.h>

#if defined(CXXRTL_INCLUDE_CAPI_IMPL) || \
    defined(CXXRTL_INCLUDE_VCD_CAPI_IMPL)
#include <cxxrtl/capi/cxxrtl_capi.cc>
#endif

#if defined(CXXRTL_INCLUDE_VCD_CAPI_IMPL)
#include <cxxrtl/capi/cxxrtl_capi_vcd.cc>
#endif

using namespace cxxrtl_yosys;

namespace cxxrtl_design {

// \top: 1
struct p_gold : public module {
	/*output*/ value<6> p_Y;
	/*input*/ value<4> p_B;
	/*input*/ value<5> p_A;
	p_gold(interior) {}
	p_gold() {
		reset();
	};

	void reset() override;

	bool eval(performer *performer = nullptr) override;

	template<class ObserverT>
	bool commit(ObserverT &observer) {
		bool changed = false;
		return changed;
	}

	bool commit() override {
		observer observer;
		return commit<>(observer);
	}

	void debug_eval();

	void debug_info(debug_items *items, debug_scopes *scopes, std::string path, metadata_map &&cell_attrs = {}) override;
}; // struct p_gold

void p_gold::reset() {
}

bool p_gold::eval(performer *performer) {
	bool converged = true;
	// cell \UUT
	p_Y = add_ss<6>(p_A, p_B);
	return converged;
}

void p_gold::debug_eval() {
}

CXXRTL_EXTREMELY_COLD
void p_gold::debug_info(debug_items *items, debug_scopes *scopes, std::string path, metadata_map &&cell_attrs) {
	assert(path.empty() || path[path.size() - 1] == ' ');
	if (scopes) {
		scopes->add(path.empty() ? path : path.substr(0, path.size() - 1), "gold", metadata_map({
			{ "top", UINT64_C(1) },
		}), std::move(cell_attrs));
	}
	if (items) {
		items->add(path, "Y", "", p_Y, 0, debug_item::OUTPUT|debug_item::DRIVEN_COMB);
		items->add(path, "B", "", p_B, 0, debug_item::INPUT|debug_item::UNDRIVEN);
		items->add(path, "A", "", p_A, 0, debug_item::INPUT|debug_item::UNDRIVEN);
	}
}

} // namespace cxxrtl_design

extern "C"
cxxrtl_toplevel cxxrtl_design_create() {
	return new _cxxrtl_toplevel { std::unique_ptr<cxxrtl_design::p_gold>(new cxxrtl_design::p_gold) };
}
