#include <gtest/gtest.h>

#include "kernel/modtools.h"
#include "kernel/rtlil.h"
#include "tests/unit/yosysSetupEnv.h"

YOSYS_NAMESPACE_BEGIN

TEST(ModIndexSwapTest, has)
{
    Design* d = new Design;
    Module* m = d->addModule(d->twines.add(std::string{"$m"}));
    Wire* o = m->addWire(d->twines.add(std::string{"$o"}), 2);
    o->port_input = true;
    Wire* i = m->addWire(d->twines.add(std::string{"$i"}), 2);
    i->port_input = true;
    m->fixup_ports();
    m->addNot(Twine{std::string{"$not"}}, i, o);
    auto mi = ModIndex(m);
    mi.reload_module();
    for (auto [sb, info] : mi.database) {
        EXPECT_TRUE(mi.database.find(sb) != mi.database.end());
    }
    m->swap_names(i, o);
    for (auto [sb, info] : mi.database) {
        EXPECT_TRUE(mi.database.find(sb) != mi.database.end());
    }
}

TEST(ModIndexDeleteTest, has)
{
    if (log_files.empty()) log_files.emplace_back(stdout);
    Design* d = new Design;
    Module* m = d->addModule(d->twines.add(std::string{"$m"}));
    Wire* w = m->addWire(d->twines.add(std::string{"$w"}));
    Wire* o = m->addWire(d->twines.add(std::string{"$o"}));
    o->port_output = true;
    m->fixup_ports();
    Cell* not_ = m->addNotGate(Twine{std::string{"$not"}}, w, o);
    auto mi = ModIndex(m);
    mi.reload_module();
    mi.dump_db();
    Wire* a = m->addWire(d->twines.add(std::string{"\\a"}));
    not_->setPort(TW::A, a);
    EXPECT_TRUE(mi.ok());
}

YOSYS_NAMESPACE_END
