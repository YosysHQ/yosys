import os
import sys
import re

from pathlib import Path

COEFF_RE = re.compile(r"y\d+\s*=\s*x\s*\*\s*\((-?)\d+\'sd(\d+)\);")

class TestFile:
	def __init__(self, path: Path):
		self.path = path
		self.coeffs = self.parse_coeffs()

	def parse_coeffs(self) -> list[int]:
		coeffs = []
		with open(self.path, "r") as f:
			lines = f.readlines()
			for line in lines:
				m = COEFF_RE.match(line)
				if m:
					sign = -1 if m.group(1) == "-" else 1
					num = int(m.group(2)) * sign
					coeffs.append(num)
		return coeffs

	def profile_yosys(self, yosys_path: Path):
		pass

def main():
	if not "YOSYS" in os.environ:
		raise Exception("Set YOSYS environment variable to absolute path of yosys binary")

	yosys_bin = Path(os.environ["YOSYS"])
	root_dir = Path(sys.argv[0]).parent
	test_files = [TestFile(root_dir / "verilog" / Path(f)) for f in os.listdir(root_dir / "verilog")]

	for test_file in test_files:
		print(test_file.path)

if __name__ == "__main__":
	main()
