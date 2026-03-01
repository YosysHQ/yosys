#include <gtest/gtest.h>

#include "kernel/modtools.h"
#include "kernel/rtlil.h"

YOSYS_NAMESPACE_BEGIN

TEST(ModIndexTest, swap)
{
    Design* d = new Design;
    Module* m = d->addModule("$m");
    Wire* o = m->addWire("$o", 2);
    o->port_input = true;
    Wire* i = m->addWire("$i", 2);
    i->port_input = true;
    m->fixup_ports();
    m->addNot("$not", i, o);
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

TEST(ModIndexTest, modify)
{
    if (log_files.empty()) log_files.emplace_back(stdout);
    Design* d = new Design;
    Module* m = d->addModule("$m");
    Wire* w = m->addWire("$w");
    Wire* o = m->addWire("$o");
    o->port_output = true;
    m->fixup_ports();
    Cell* not_ = m->addNotGate("$not", w, o);
    auto mi = ModIndex(m);
    mi.reload_module();
    mi.dump_db();
    Wire* a = m->addWire("\\a");
    not_->setPort(ID::A, a);
    EXPECT_TRUE(mi.ok());
}

YOSYS_NAMESPACE_END
