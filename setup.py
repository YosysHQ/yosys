#!/usr/bin/env python3
# Copyright (C) 2024 Efabless Corporation
#
# Permission to use, copy, modify, and/or distribute this software for any
# purpose with or without fee is hereby granted, provided that the above
# copyright notice and this permission notice appear in all copies.
#
# THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
# WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
# MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
# ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
# WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
# ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
# OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
import os
import re
import shlex
import shutil
from pathlib import Path
from setuptools import setup, Extension

import pybind11
from pybind11.setup_helpers import build_ext

__yosys_root__ = Path(__file__).parent

yosys_version_rx = re.compile(r"YOSYS_VER\s*:=\s*([\w\-\+\.]+)")

with open(__yosys_root__ / "Makefile", encoding="utf8") as f:
    # Extract and convert + to patch version
    version = yosys_version_rx.search(f.read())[1].replace("+", ".")


class libyosys_so_ext(Extension):
    def __init__(
        self,
    ) -> None:
        super().__init__(
            "libyosys.so",
            [],
        )

        # when iterating locally, you probably want to set this variable
        # to avoid mass rebuilds bec of pybind11's include path changing
        pybind_include = os.getenv("_FORCE_PYBIND_INCLUDE", pybind11.get_include())

        self.args = [
            f"PYBIND11_INCLUDE={pybind_include}",
            "ENABLE_PYOSYS=1",
            # Would need to be installed separately by the user
            "ENABLE_TCL=0",
            "ENABLE_READLINE=0",
            "ENABLE_EDITLINE=0",
            # Always compile and include ABC in wheel
            "ABCEXTERNAL=",
            # Show compile commands
            "PRETTY=0",
        ]

    def custom_build(self, bext: build_ext):
        make_flags_split = shlex.split(os.getenv("makeFlags", ""))
        # abc linking takes a lot of memory, best get it out of the way first
        bext.spawn(
            [
                "make",
                f"-j{os.cpu_count() or 1}",
                "yosys-abc",
                *make_flags_split,
                *self.args,
            ]
        )
        # build libyosys and share with abc out of the way
        bext.spawn(
            [
                "make",
                f"-j{os.cpu_count() or 1}",
                self.name,
                "share",
                *make_flags_split,
                *self.args,
            ]
        )
        ext_fullpath = Path(bext.get_ext_fullpath(self.name))
        build_path = ext_fullpath.parents[1]
        pyosys_path = build_path / "pyosys"
        os.makedirs(pyosys_path, exist_ok=True)

        # libyosys.so
        target = pyosys_path / self.name
        shutil.copy(self.name, target)
        bext.spawn(["strip", "-S", str(target)])

        # yosys-abc
        yosys_abc_target = pyosys_path / "yosys-abc"
        shutil.copy("yosys-abc", yosys_abc_target)
        bext.spawn(["strip", "-S", str(yosys_abc_target)])

        # share directory
        share_target = pyosys_path / "share"
        try:
            shutil.rmtree(share_target)
        except FileNotFoundError:
            pass

        shutil.copytree("share", share_target)


class custom_build_ext(build_ext):
    def build_extension(self, ext) -> None:
        if not hasattr(ext, "custom_build"):
            return super().build_extension(ext)
        return ext.custom_build(self)


with open(__yosys_root__ / "README.md", encoding="utf8") as f:
    long_description = f.read()

setup(
    name="pyosys",
    packages=["pyosys"],
    version=version,
    description="Python access to libyosys",
    long_description=long_description,
    long_description_content_type="text/markdown",
    license="MIT",
    classifiers=[
        "Programming Language :: Python :: 3",
        "Intended Audience :: Developers",
        "Operating System :: POSIX :: Linux",
        "Operating System :: MacOS :: MacOS X",
    ],
    python_requires=">=3.8",
    ext_modules=[libyosys_so_ext()],
    cmdclass={
        "build_ext": custom_build_ext,
    },
)
