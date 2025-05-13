#include "kernel/yosys.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct RaiseErrorPass : public Pass {
	RaiseErrorPass() : Pass("raise_error", "raise errors from attributes") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    raise_error [options] [selection]\n");
		log("\n");
		log("Test error handling by raising arbitrary errors. This pass iterates over the\n");
		log("design (or selection of it) checking for objects with the 'raise_error'\n");
		log("attribute set. Assigning 'raise_error' to a string more than one character long\n");
		log("will log that string as an error message before exiting. Assigning 'raise_error'\n");
		log("to an integer (less than 256) will exit with that value as the exit code.\n");
		log("\n");
		log("    -stderr\n");
		log("        Log error messages directly to stderr instead of using 'log_error'.\n");
		log("\n");
	}
	void execute(vector<string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing RAISE_ERROR pass.\n");

		bool use_stderr = false;

		int argidx;
		for (argidx = 1; argidx < GetSize(args); argidx++)
		{
			if (args[argidx] == "-stderr") {
				use_stderr = true;
				continue;
			}
			break;
		}

		extra_args(args, argidx, design, true);

		RTLIL::NamedObject *err_obj = nullptr;
		
		for (auto mod : design->all_selected_modules()) {
			if (mod->has_attribute(ID::raise_error)) {
				err_obj = mod->clone();
				break;
			}
			for (auto memb : mod->selected_members()) {
				if (memb->has_attribute(ID::raise_error)) {
					err_obj = memb;
					break;
				}
			}
			if (err_obj != nullptr) break;
		}

		if (err_obj != nullptr) {
			log("Raising error from '%s'.\n", log_id(err_obj));
			auto err_no = err_obj->attributes[ID::raise_error].as_int();
			if (err_no < 256) {
				log_flush();
			} else {
				auto err_msg = err_obj->get_string_attribute(ID::raise_error);
				if (use_stderr) {
					std::cerr << err_msg << std::endl;
					err_no = 1;
				} else {
					log_error("%s\n", err_msg.c_str());
				}
			}
		#if defined(_MSC_VER)
			_exit(err_no);
		#else
			_Exit(err_no);
		#endif
		} else {
			log("'raise_error' attribute not found\n");
		}
	}
} RaiseErrorPass;

PRIVATE_NAMESPACE_END
