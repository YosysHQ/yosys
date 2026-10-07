import os
import sys
import re
import subprocess
import time
import statistics

from pathlib import Path
from dataclasses import dataclass

COEFF_RE = re.compile(r"y\d+\s*=\s*x\s*\*\s*\((-?)\d+\'sd(\d+)\);")
STAT_RE = re.compile(r"^\s*(\d+)\s+\$(\w+)\s*$", re.MULTILINE)
DEPTH_RE = re.compile(r"^\s*mcm: .* -> \d+ adder\(s\), depth (\d+),", re.MULTILINE)
ACM_COST_RE = re.compile(r"^// Cost: (\d+) adds/subtracts (\d+) shifts (\d+) negations$", re.MULTILINE)
ACM_DEPTH_RE = re.compile(r"^// Depth: (\d+)$", re.MULTILINE)

MAX_TESTS = 10

@dataclass
class ProfileResult:
	seconds: float
	adds_subs: int
	negations: int
	depth: int | None
	shifts: int | None = None

	def __str__(self) -> str:
		depth = self.depth if self.depth is not None else "unknown"
		shifts = f", {self.shifts} shifts" if self.shifts is not None else ""
		return f"{self.seconds:.3f}s, {self.adds_subs} adds/subtracts, {self.negations} negations{shifts}, depth {depth}"

def parse_yosys(stdout: str, seconds: float) -> ProfileResult:
	if not re.search(r"^=== .+ ===$", stdout, re.MULTILINE):
		raise ValueError("Missing Yosys statistics")
	cells: dict[str, int] = {}
	for count, cell in STAT_RE.findall(stdout):
		cells[cell] = cells.get(cell, 0) + int(count)
	depths = [int(depth) for depth in DEPTH_RE.findall(stdout)]
	return ProfileResult(seconds, cells.get("add", 0) + cells.get("sub", 0), cells.get("neg", 0), max(depths, default=None))

def parse_acm(stdout: str, seconds: float) -> ProfileResult:
	cost = ACM_COST_RE.search(stdout)
	depth = ACM_DEPTH_RE.search(stdout)
	if cost is None or depth is None:
		raise ValueError("Missing ACM cost or depth")
	adds_subs, shifts, negations = map(int, cost.groups())
	return ProfileResult(seconds, adds_subs, negations, int(depth.group(1)), shifts)

def run_profile(args: list[str], log_path: Path) -> tuple[str, float]:
	log_path.parent.mkdir(parents=True, exist_ok=True)
	start = time.perf_counter()
	res = subprocess.run(args, capture_output=True, text=True)
	seconds = time.perf_counter() - start
	log_path.write_text(res.stdout)
	res.check_returncode()
	return res.stdout, seconds

class TestFile:
	def __init__(self, path: Path):
		self.path = path
		self.coeffs = self.parse_coeffs()
		self.results_dir = path.parent.parent / "results" / path.stem

	def parse_coeffs(self) -> list[str]:
		coeffs = []
		with open(self.path, "r") as f:
			lines = f.readlines()
			for line in lines:
				m = COEFF_RE.search(line)
				if m:
					sign = -1 if m.group(1) == "-" else 1
					num = str(int(m.group(2)) * sign)
					coeffs.append(num)
		return coeffs

	def profile_yosys(self, yosys_path: Path) -> ProfileResult:
		verilog_path = self.results_dir / "yosys.v"
		stdout, seconds = run_profile(
			[str(yosys_path), "-p", f'read_verilog "{self.path}"; mcm; stat; write_verilog "{verilog_path}"'],
			self.results_dir / "yosys.log",
		)
		return parse_yosys(stdout, seconds)

	def profile_acm(self, acm_path: Path) -> ProfileResult:
		args = [str(acm_path), "-b", "30", *self.coeffs, "-gc", "-seed", "1"]
		stdout, seconds = run_profile(args, self.results_dir / "acm.log")
		return parse_acm(stdout, seconds)

	def profile(self, yosys_path: Path, acm_path: Path):
		yosys = self.profile_yosys(yosys_path)
		acm = self.profile_acm(acm_path)
		coeffs = self.coeffs
		ratio = yosys.seconds / acm.seconds
		items = [
			("yosys", yosys),
			("hcub_paper", acm),
			("ratio", f"{ratio:.2f}"),
			("coeffs", ", ".join(coeffs)),
		]
		print_table(self.path.stem, items)
		return yosys, acm

def print_table(title: str, items: list[tuple[str, str]]) -> None:
	print(title)
	longest_name = 0
	for name, value in items:
		longest_name = max(longest_name, len(name))
	for name, value in items:
		num_spaces = longest_name - len(name)
		print(f"\t{name}:{' ' * num_spaces} {value}")
	print()

def main():
	if not "YOSYS" in os.environ:
		raise Exception("Set YOSYS environment variable to absolute path of yosys binary")

	yosys_bin = Path(os.environ["YOSYS"])
	root_dir = Path(sys.argv[0]).parent
	test_files = [TestFile(root_dir / "verilog" / Path(f)) for f in os.listdir(root_dir / "verilog")]
	acm_path = root_dir / "synth" / "acm"

	results = []

	for idx, test_file in enumerate(test_files):
		if MAX_TESTS is not None and idx >= MAX_TESTS:
			break

		yosys_res, acm_res = test_file.profile(yosys_bin, acm_path)
		results.append((yosys_res, acm_res))

	# 1000ms = 1s
	timescale = 1000

	avg_yosys_runtime = sum(res.seconds * timescale for res, _ in results) / len(results)
	avg_acm_runtime = sum(res.seconds * timescale for _, res in results) / len(results)
	stdev_yosys_runtime = statistics.stdev([res.seconds * timescale for res, _ in results])
	stdev_acm_runtime = statistics.stdev([res.seconds * timescale for _, res in results])

	avg_runtime_ratio = avg_yosys_runtime / avg_acm_runtime

	items = [
		("Avg Yosys runtime (ms)", f"{avg_yosys_runtime:.2f}"),
		("Avg hcub_paper runtime (ms)", f"{avg_acm_runtime:.2f}"),
		("Stdev Yosys runtime (ms)", f"{stdev_yosys_runtime:.2f}"),
		("Stdev hcub_paper runtime (ms)", f"{stdev_acm_runtime:.2f}"),
		("Average hcub_paper Speed Up", f"{avg_runtime_ratio:.2f}")
	]
	print_table("Results", items)

if __name__ == "__main__":
	main()
