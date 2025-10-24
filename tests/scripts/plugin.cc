#include "kernel/yosys.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct TestArgsPass : public Pass {
    TestArgsPass() : Pass("test_args", "dummy pass to test arg parsing") {
        internal();
    }
    void execute(std::vector<std::string> args, RTLIL::Design*) override {
        int argidx;
        for (argidx = 0; argidx < GetSize(args); argidx++)
        {
            log("%s\n", args[argidx]);
        }
    }
} TestArgsPass;

struct TestArgsFrontend : public Frontend {
    TestArgsFrontend() : Frontend("test_args", "dummy frontend to test arg parsing") {
        internal();
    }
    void execute(std::istream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *) override {
        int argidx;
        log("pass: %s\n", args[0]);
        for (argidx = 1; argidx < GetSize(args); argidx++) {
            if (args[argidx] == "-arg" && argidx+1 < GetSize(args)) {
                log("arg: %s\n", args[++argidx]);
                continue;
            }
            break;
        }
		extra_args(f, filename, args, argidx);
        log("filename: %s\n", filename);
    }
} TestArgsFrontend;

struct TestArgsBackend : public Backend {
    TestArgsBackend() : Backend("test_args", "dummy backend to test arg parsing") {
        internal();
    }
    void execute(std::ostream *&f, std::string filename,  std::vector<std::string> args, RTLIL::Design *) override {
        int argidx;
        log("pass: %s\n", args[0]);
        for (argidx = 1; argidx < GetSize(args); argidx++) {
            if (args[argidx] == "-arg" && argidx+1 < GetSize(args)) {
                log("arg: %s\n", args[++argidx]);
                continue;
            }
            break;
        }
		extra_args(f, filename, args, argidx);
        log("filename: %s\n", filename);
    }
} TestArgsBackend;

PRIVATE_NAMESPACE_END
