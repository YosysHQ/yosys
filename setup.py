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
from setuptools import setup, Extension
from setuptools.command.build_ext import build_ext

__dir__ = os.path.dirname(os.path.abspath(__file__))

yosys_version_rx = re.compile(r"YOSYS_VER\s*:=\s*([\w\-\+\.]+)")

version = yosys_version_rx.search(
    open(os.path.join(__dir__, "Makefile"), encoding="utf8").read()
)[1].replace(
    "+", "."
)  # Convert to patch version


class libyosys_so_ext(Extension):
    def __init__(
        self,
    ) -> None:
        super().__init__(
            "libyosys.so",
            [],
        )
        self.args = [
            "ENABLE_PYOSYS=1",
            # Wheel meant to be imported from interpreter
            "ENABLE_PYTHON_CONFIG_EMBED=0",
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
        bext.spawn(
            [
                "make",
                f"-j{os.cpu_count() or 1}",
                self.name,
                "yosys-abc",
                "share",
            ]
            + shlex.split(os.getenv("makeFlags", ""))
            + self.args
        )
        build_path = os.path.dirname(os.path.dirname(bext.get_ext_fullpath(self.name)))
        pyosys_path = os.path.join(build_path, "pyosys")
        os.makedirs(pyosys_path, exist_ok=True)

        # libyosys.so
        target = os.path.join(pyosys_path, os.path.basename(self.name))
        shutil.copy(self.name, target)
        bext.spawn(["strip", "-S", target])

        # yosys-abc
        yosys_abc_target = os.path.join(pyosys_path, "yosys-abc")
        shutil.copy("yosys-abc", yosys_abc_target)
        bext.spawn(["strip", "-S", "yosys-abc"])

        # share directory
        share_target = os.path.join(pyosys_path, "share")
        try:
            shutil.rmtree(share_target)
        except FileNotFoundError:
            pass

        shutil.copytree("share", share_target)

        # I don't know how debug info is getting here.


class custom_build_ext(build_ext):
    def build_extension(self, ext) -> None:
        if not hasattr(ext, "custom_build"):
            return super().build_extension(ext)
        return ext.custom_build(self)


setup(
    name="pyosys",
    packages=["pyosys"],
    version=version,
    description="Python access to libyosys",
    long_description=open(os.path.join(__dir__, "README.md")).read(),
    long_description_content_type="text/markdown",
    install_requires=["wheel", "setuptools"],
    classifiers=[
        "License :: OSI Approved :: MIT License",
        "Programming Language :: Python :: 3",
        "Intended Audience :: Developers",
        "Operating System :: POSIX :: Linux",
        "Operating System :: MacOS :: MacOS X",
    ],
    package_dir={"pyosys": "misc"},
    python_requires=">=3.8",
    ext_modules=[libyosys_so_ext()],
    cmdclass={
        "build_ext": custom_build_ext,
    },
)
