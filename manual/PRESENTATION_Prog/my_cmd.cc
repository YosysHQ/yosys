#include "kernel/yosys.h"
#include "kernel/sigtools.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct MyPass : public Pass {
    MyPass() : Pass("my_cmd", "just a simple test") { }
    void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
    {
        log("Arguments to my_cmd:\n");
        for (auto &arg : args)
            log("  %s\n", arg.c_str());

        log("Modules in current design:\n");
        for (auto mod : design->modules())
            log("  %s (%zd wires, %zd cells)\n", log_id(mod),
                    GetSize(mod->wires()), GetSize(mod->cells()));
    }
} MyPass;


struct Test1Pass : public Pass {
    Test1Pass() : Pass("test1", "creating the absval module") { }
    void execute(std::vector<std::string>, RTLIL::Design *design) YS_OVERRIDE
    {
        if (design->has("\\absval") != 0)
            log_error("A module with the name absval already exists!\n");

        RTLIL::Module *module = design->addModule("\\absval");
        log("Name of this module: %s\n", log_id(module));

        RTLIL::Wire *a = module->addWire("\\a", 4);
        a->port_input = true;
        a->port_id = 1;

        RTLIL::Wire *y = module->addWire("\\y", 4);
        y->port_output = true;
        y->port_id = 2;

        RTLIL::Wire *a_inv = module->addWire(NEW_ID, 4);
        module->addNeg(NEW_ID, a, a_inv, true);
        module->addMux(NEW_ID, a, a_inv, RTLIL::SigSpec(a, 3), y);

	module->fixup_ports();
    }
} Test1Pass;


struct Test2Pass : public Pass {
    Test2Pass() : Pass("test2", "demonstrating sigmap on test module") { }
    void execute(std::vector<std::string>, RTLIL::Design *design) YS_OVERRIDE
    {
        if (design->selection_stack.back().empty())
            log_cmd_error("This command can't operator on an empty selection!\n");

        RTLIL::Module *module = design->modules_.at("\\test");

        RTLIL::SigSpec a(module->wire("\\a")), x(module->wire("\\x")), y(module->wire("\\y"));
        log("%d %d %d\n", a == x, x == y, y == a); // will print "0 0 0"

        SigMap sigmap(module);
        log("%d %d %d\n", sigmap(a) == sigmap(x), sigmap(x) == sigmap(y),
                          sigmap(y) == sigmap(a)); // will print "1 1 1"

        log("Mapped signal x: %s\n", log_signal(sigmap(x)));

        log_header(design, "Doing important stuff!\n");
        log_push();
        for (int i = 0; i < 10; i++)
            log("Log message #%d.\n", i);
        log_pop();
    }
} Test2Pass;

PRIVATE_NAMESPACE_END
