/*
 * Copyright 2020-2022 F4PGA Authors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * SPDX-License-Identifier: Apache-2.0
 *
 */

#include "kernel/sigtools.h"
#include "kernel/yosys.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct QuicklogicEqnPass : public Pass {
    QuicklogicEqnPass() : Pass("quicklogic_eqn", "Quicklogic: Calculate equations for luts") {}
    void help() override
    {
        log("\n");
        log("    quicklogic_eqn [selection]\n");
        log("\n");
        log("Calculate equations for luts since bitstream generator depends on it.\n");
        log("\n");
    }

    Const init2eqn(Const init, int inputs)
    {
        std::string init_bits = init.as_string();
        const char *names[] = {"I0", "I1", "I2", "I3", "I4"};

        std::string eqn;
        int width = (int)pow(2, inputs);
        for (int i = 0; i < width; i++) {
            if (init_bits[width - 1 - i] == '1') {
                eqn += "(";
                for (int j = 0; j < inputs; j++) {
                    if (i & (1 << j))
                        eqn += names[j];
                    else
                        eqn += std::string("~") + names[j];

                    if (j != (inputs - 1))
                        eqn += "*";
                }
                eqn += ")+";
            }
        }
        if (eqn.empty())
            return Const("0");
        eqn = eqn.substr(0, eqn.length() - 1);
        return Const(eqn);
    }

    void execute(std::vector<std::string> args, RTLIL::Design *design) override
    {
        log_header(design, "Executing Quicklogic_EQN pass (calculate equations for luts).\n");

        extra_args(args, args.size(), design);

        int cnt = 0;
        for (auto module : design->selected_modules()) {
            for (auto cell : module->selected_cells()) {
                if (cell->type == ID(LUT1)) {
                    cell->setParam(ID(EQN), init2eqn(cell->getParam(ID::INIT), 1));
                    cnt++;
                }
                if (cell->type == ID(LUT2)) {
                    cell->setParam(ID(EQN), init2eqn(cell->getParam(ID::INIT), 2));
                    cnt++;
                }
                if (cell->type == ID(LUT3)) {
                    cell->setParam(ID(EQN), init2eqn(cell->getParam(ID::INIT), 3));
                    cnt++;
                }
                if (cell->type == ID(LUT4)) {
                    cell->setParam(ID(EQN), init2eqn(cell->getParam(ID::INIT), 4));
                    cnt++;
                }
                if (cell->type == ID(LUT5)) {
                    cell->setParam(ID(EQN), init2eqn(cell->getParam(ID::INIT), 5));
                    cnt++;
                }
            }
        }
        log_header(design, "Updated %d of LUT* elements with equation.\n", cnt);
    }
} QuicklogicEqnPass;

PRIVATE_NAMESPACE_END
