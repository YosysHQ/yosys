#!/usr/bin/env python3

from pathlib import Path
import sys
sys.path.append("..")

import gen_tests_makefile

techlibs_dir = Path("../../techlibs")

# Architecture-specific defines
defines = {
    "ice40": ["ICE40_HX", "ICE40_LP", "ICE40_U"]
}

def archs():
    # Loop over architectures
    for arch in techlibs_dir.iterdir():
        if not arch.is_dir():
            continue
        arch_name = arch.name

        for path in arch.rglob("cells_sim.v"):
            rel_parts = path.relative_to(techlibs_dir).parts
            target_base = "_".join(rel_parts[-len(rel_parts):]).replace(".v", "")
            path_str = str(path)
            if arch_name in defines:
                for defn in defines[arch_name]:
                    target_name = f"{target_base}_{defn}"
                    cmd = f"iverilog -t null -I{arch} -D{defn} -DNO_ICE40_DEFAULT_ASSIGNMENTS {path_str}"
                    gen_tests_makefile.generate_target(target_name, cmd)
            else:
                target_name = f"{target_base}"
                cmd = f"iverilog -t null -I{arch} -g2005-sv {path_str}"
                gen_tests_makefile.generate_target(target_name, cmd)

def common():
    for path in ["../../techlibs/common/simcells.v", "../../techlibs/common/simlib.v"]:
        path_obj = Path(path)
        target_name = path_obj.stem
        cmd = f"iverilog -t null {path}"
        gen_tests_makefile.generate_target(target_name, cmd)

def main():
    def callback():
        archs()
        common()

    gen_tests_makefile.generate_custom(callback)

if __name__ == "__main__":
    main()
