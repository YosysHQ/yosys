# To build a wheel with additional CMake options, use `--build-option`, e.g.:
#
# 	python -m build -w -Ccmake=-DYOSYS_COMPILER_LAUNCHER=ccache
#   pip install -Ccmake=-DYOSYS_COMPILER_LAUNCHER=ccache .

import os
import sys
import pathlib
import tarfile
import tempfile
import subprocess
import sysconfig
from email.policy import EmailPolicy
from email.message import EmailMessage
from wheel.wheelfile import WheelFile


PROJECT_NAME = "pyosys"
PROJECT_VERSION = subprocess.check_output([
	"cmake",
	f"-DCMAKE_SOURCE_DIR={os.getcwd()}",
	"-P", "cmake/GetPyosysVersion.cmake"
], encoding="ascii").strip()
DIST_NAME = f"{PROJECT_NAME}-{PROJECT_VERSION}"

# https://packaging.python.org/en/latest/specifications/platform-compatibility-tags/
if sys.implementation.name == "cpython":
	PYTHON_TAG = f"cp{sysconfig.get_config_var('py_version_nodot')}"
else:
	raise NotImplementedError("unsupported Python implementation")
PLATFORM_TAG = sysconfig.get_platform().replace("-", "_")
COMPAT_TAG = f"{PYTHON_TAG}-none-{PLATFORM_TAG}"


def compile_pyosys(cmake_options=[], parallel=os.cpu_count() or 1):
	install_dir = tempfile.TemporaryDirectory(prefix="pyosys_install")
	with tempfile.TemporaryDirectory(prefix="pyosys_build") as build_dir:
		subprocess.check_call([
			"cmake",
			"-S", ".",
			"-B", build_dir,
			"-DCMAKE_BUILD_TYPE=Release",
			f"-DPython3_EXECUTABLE={sys.executable}",
			"-DYOSYS_WITH_PYTHON=ON",
			"-DYOSYS_INSTALL_DRIVER=OFF",
			"-DYOSYS_INSTALL_LIBRARY=OFF",
			"-DYOSYS_INSTALL_PYTHON=ON",
			f"-DCMAKE_INSTALL_PREFIX={install_dir.name}",
			f"-DYOSYS_INSTALL_PYTHON_SITEDIR=python",
			"-DYOSYS_BUILD_PYTHON_ONLY=ON",
			*cmake_options,
		])
		subprocess.check_call([
			"cmake",
			"--build", build_dir,
			"-t", "pyosys",
			f"-j{parallel}",
		])
		subprocess.check_call([
			"cmake",
			"--install", build_dir,
			"--strip",
		])
	return install_dir


def make_message(headers, payload=None):
	msg = EmailMessage(policy=EmailPolicy(max_line_length=0))
	for name, value in headers:
		if isinstance(value, list):
			for value_part in value:
				msg[name] = value_part
		else:
			msg[name] = value
	if payload:
		msg.set_payload(payload)
	return bytes(msg)


def build_sdist(sdist_dir, config_settings=None):
	sdist_filename = f"{DIST_NAME}.tar.gz"

	with tarfile.open(pathlib.Path(sdist_dir) / sdist_filename, "w:gz",
			format=tarfile.PAX_FORMAT) as sdist:
		def exclude_build(entry):
			name = entry.name.removeprefix(f"{DIST_NAME}/")
			if name in (".cache", "build", "dist"):
				return
			if os.path.basename(name) in (".git", "__pycache__"):
				return
			return entry
		sdist.add(os.getcwd(), arcname=DIST_NAME, filter=exclude_build)

	return sdist_filename


def get_metadata_files():
	with open("README.md", "rb") as readme:
		long_description = readme.read()

	return {
		"WHEEL": make_message([
			("Wheel-Version", "1.0"),
			("Generator", "pyosys build backend"),
			("Root-Is-Purelib", "false"),
			("Tag", [COMPAT_TAG]),
		]),
		"METADATA": make_message([
			("Metadata-Version", "2.4"),
			("Name", PROJECT_NAME),
			("Version", PROJECT_VERSION),
			("Summary", "Python access to libyosys"),
			("Description-Content-Type", "text/markdown"),
			("License-Expression", "MIT"),
			("Classifier", "Programming Language :: Python :: 3"),
			("Classifier", "Intended Audience :: Developers"),
			("Classifier", "Operating System :: POSIX :: Linux"),
			("Classifier", "Operating System :: MacOS :: MacOS X"),
			("Requires-Python", ">=3.10"),
		], long_description)
	}


def prepare_metadata_for_build_wheel(metadata_directory, config_settings=None):
	os.mkdir(f"{metadata_directory}/{DIST_NAME}.dist-info")

	for filename, contents in get_metadata_files().items():
		with open(f"{metadata_directory}/{DIST_NAME}.dist-info/{filename}", "wb") as f:
			f.write(contents)

	return f"{DIST_NAME}.dist-info"


def build_wheel(wheel_dir, config_settings=None, metadata_directory=None):
	wheel_filename = f"{DIST_NAME}-{COMPAT_TAG}.whl"

	with WheelFile(pathlib.Path(wheel_dir) / wheel_filename, "w") as wheel:
		for filename, contents in get_metadata_files().items():
			wheel.writestr(f"{DIST_NAME}.dist-info/{filename}", contents)

		cmake_options = []
		if config_settings is not None:
			if cmake_options := config_settings.get("cmake", cmake_options):
				if isinstance(cmake_options, str):
					cmake_options = [cmake_options]
		with compile_pyosys(cmake_options) as install_dir:
			wheel.write_files(pathlib.Path(install_dir) / "python")

	return wheel_filename
