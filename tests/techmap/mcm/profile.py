import os
import sys
import re
import subprocess
import time
import statistics
import random

from enum import Enum
from textwrap import dedent

from pathlib import Path
from dataclasses import dataclass

COEFF_RE = re.compile(r"y\d+\s*=\s*x\s*\*\s*\((-?)\d+\'sd(\d+)\);")
STAT_RE = re.compile(r"^\s*(\d+)\s+\$(\w+)\s*$", re.MULTILINE)
DEPTH_RE = re.compile(r"^\s*mcm: .* -> \d+ adder\(s\), depth (\d+),", re.MULTILINE)
ACM_COST_RE = re.compile(r"^// Cost: (\d+) adds/subtracts (\d+) shifts (\d+) negations$", re.MULTILINE)
ACM_DEPTH_RE = re.compile(r"^// Depth: (\d+)$", re.MULTILINE)

@dataclass
class ProfileResult:
	seconds: float
	adds_subs: int
	negations: int
	depth: int | None
	shifts: int | None = None
	mul: int = 0

	def time(self) -> str:
		return f"{self.seconds:.3f}s"

	def stats(self) -> str:
		depth = self.depth if self.depth is not None else "unknown"
		return f"add+sub={self.adds_subs}, mul={self.mul}, depth={depth}"

def parse_yosys(stdout: str, seconds: float) -> ProfileResult:
	if not re.search(r"^=== .+ ===$", stdout, re.MULTILINE):
		raise ValueError("Missing Yosys statistics")
	cells: dict[str, int] = {}
	for count, cell in STAT_RE.findall(stdout):
		cells[cell] = cells.get(cell, 0) + int(count)
	depths = [int(depth) for depth in DEPTH_RE.findall(stdout)]
	return ProfileResult(seconds, cells.get("add", 0) + cells.get("sub", 0), cells.get("neg", 0), max(depths, default=None), mul=cells.get("mul", 0))

def parse_acm(stdout: str, seconds: float) -> ProfileResult:
	cost = ACM_COST_RE.search(stdout)
	depth = ACM_DEPTH_RE.search(stdout)
	if cost is None or depth is None:
		raise ValueError("Missing ACM cost or depth")
	adds_subs, shifts, negations = map(int, cost.groups())
	mul = len(re.findall(r"^\s*t\d+\s*=\s*cmul\(", stdout, re.MULTILINE))
	return ProfileResult(seconds, adds_subs, negations, int(depth.group(1)), shifts, mul)

def run_profile(args: list[str], log_path: Path) -> tuple[str, float]:
	log_path.parent.mkdir(parents=True, exist_ok=True)
	start = time.perf_counter()
	res = subprocess.run(args, capture_output=True, text=True)
	seconds = time.perf_counter() - start
	log_path.write_text(res.stdout)
	res.check_returncode()
	return res.stdout, seconds


class Coeff:
	def __init__(self, number: int, bit_width: int):
		self.number = number
		self.bit_width = bit_width

	def __str__(self):
		return f"{self.number}"

class Test:
	def __init__(self, input_width: int, coeffs: list[Coeff], idx: int, output_dir: Path):
		self.coeffs = coeffs
		self.input_width = input_width
		self.results_dir = output_dir / f"test_{idx}"
		self.verilog_file = self.results_dir / f"unoptimized.v"

		self.generate_v_file()

	def generate_v_file(self) -> None:
		self.results_dir.mkdir(parents=True, exist_ok=True)


		file = "\n".join([
		    "module unoptimized(",
		    f"    input wire signed [{self.input_width - 1}:0] x,",
		    ",\n".join(
		        f"    output wire signed [{c.bit_width+self.input_width-1}:0] y{i}"
		        for i, c in enumerate(self.coeffs)
		    ),
		    ");",
		    "\n".join(
				f"    assign y{i} = x * ({'-' if c.number < 0 else ''}{self.input_width-1}'sd{abs(c.number)});"
		        for i, c in enumerate(self.coeffs)
		    ),
		    "endmodule",
		    "",
		])

		with open(self.verilog_file, "w") as f:
			f.write(file)

	def profile_yosys(self, yosys_path: Path) -> ProfileResult:
		verilog_path = self.results_dir / "yosys.v"
		stdout, seconds = run_profile(
			[str(yosys_path), "-p", f'read_verilog "{self.verilog_file}"; mcm -depth 16 -search_budget 200000000; stat; write_verilog "{verilog_path}"'],
			self.results_dir / "yosys.log",
		)
		return parse_yosys(stdout, seconds)

	def profile_acm(self, acm_path: Path) -> ProfileResult:
		coeffs = [str(coeff) for coeff in self.coeffs]
		args = [str(acm_path), "-b", "30", *coeffs, "-gc", "-seed", "1"]
		stdout, seconds = run_profile(args, self.results_dir / "acm.log")
		return parse_acm(stdout, seconds)

	def profile(self, yosys_path: Path, acm_path: Path, idx: int):
		yosys = self.profile_yosys(yosys_path)
		acm = self.profile_acm(acm_path)
		coeffs = [str(coeff) for coeff in self.coeffs]
		ratio = yosys.seconds / acm.seconds
		items = [
			("yosys runtime", yosys.time()),
			("hcub_paper runtime", acm.time()),
			("yosys stats", yosys.stats()),
			("hcub_paper stats", acm.stats()),
			("runtime ratio", f"{ratio:.2f}"),
			("coeffs", ", ".join(coeffs)),
		]
		print_table(f"Test {idx}", items)
		return yosys, acm

def print_table(title: str, items: list[tuple[str, str]]) -> None:
	print(title)
	longest_name = 0
	for name, value in items:
		longest_name = max(longest_name, len(name))
	for name, value in items:
		num_spaces = longest_name - len(name)
		value = str(value).replace("\n", "\n\t" + " " * (longest_name + 2))
		print(f"\t{name}:{' ' * num_spaces} {value}")
	print()

class Cmp(Enum):
		Better = 1
		Same = 2
		Worse = 3

def cmp(yosys: ProfileResult, acm: ProfileResult) -> Cmp:
	if yosys.mul > acm.mul:
		return Cmp.Worse
	elif yosys.mul < acm.mul:
		return Cmp.Better

	if yosys.adds_subs > acm.adds_subs:
		return Cmp.Worse
	elif yosys.adds_subs < acm.adds_subs:
		return Cmp.Better

	return Cmp.Same

def bit_width(val: int):
	return len(bin(val)) - 2

def generate_coeffs(rng: random.Random, number_tests: int, length_range: tuple[int, int], value_range: tuple[int, int], seed=42) -> list[list[Coeff]]:
	rng.seed(seed)
	coeffs = [sample_coeff(rng, length_range, value_range) for idx in range(number_tests)]
	return coeffs

# smaller a means proportially more larger values and fewer smaller values
# larger scale shifts all values upwards
# the distrition is the following
# p(x) ~ 1 - x^(-a)
def sample_coeff(
    rng: random.Random,
    length_range: tuple[int, int],
    value_range: tuple[int, int],
    a: float = 1.5,
    scale: float = 1024,
) -> list[Coeff]:
    if a <= 1 or scale <= 0:
        raise ValueError("Require a > 1 and scale > 0")

    length = rng.randint(*length_range)
    low, high = value_range
    coeffs = []

    while len(coeffs) < length:
        magnitude = int(scale * (rng.paretovariate(a - 1) - 1))
        val = rng.choice((-1, 1)) * magnitude
        if low <= val <= high:
            coeffs.append(Coeff(val, bit_width(val)))

    return coeffs

def main():
	if not "YOSYS" in os.environ:
		raise Exception("Set YOSYS environment variable to absolute path of yosys binary")

	yosys_bin = Path(os.environ["YOSYS"])
	root_dir = Path(sys.argv[0]).parent
	acm_path = root_dir / "synth" / "acm"
	output_dir = root_dir / "results"

	number_tests = 20
	seed = 42
	rng = random.Random()

	input_bit_width = 32
	length_range = (1, 6)
	value_range = (-2_147_483_648, 2_147_483_647)

	coeffs = generate_coeffs(rng, number_tests, length_range, value_range, seed)
	results = []

	for idx, coeff in enumerate(coeffs):
		test_file = Test(input_bit_width, coeff, idx, output_dir)
		yosys_res, acm_res = test_file.profile(yosys_bin, acm_path, idx)
		results.append((yosys_res, acm_res))

	# 1000ms = 1s
	timescale = 1000

	avg_yosys_runtime = sum(res.seconds * timescale for res, _ in results) / len(results)
	avg_acm_runtime = sum(res.seconds * timescale for _, res in results) / len(results)
	stdev_yosys_runtime = statistics.stdev([res.seconds * timescale for res, _ in results])
	stdev_acm_runtime = statistics.stdev([res.seconds * timescale for _, res in results])

	avg_runtime_ratio = avg_yosys_runtime / avg_acm_runtime

	compared_results = [cmp(yosys_res, acm_res) for (yosys_res, acm_res) in results]

	num_better = len([i for i in compared_results if i == Cmp.Better])
	num_same   = len([i for i in compared_results if i == Cmp.Same])
	num_worse  = len([i for i in compared_results if i == Cmp.Worse])

	items = [
		("Avg Yosys runtime (ms)", f"{avg_yosys_runtime:.2f}"),
		("Avg hcub_paper runtime (ms)", f"{avg_acm_runtime:.2f}"),
		("Stdev Yosys runtime (ms)", f"{stdev_yosys_runtime:.2f}"),
		("Stdev hcub_paper runtime (ms)", f"{stdev_acm_runtime:.2f}"),
		("Average hcub_paper Speed Up", f"{avg_runtime_ratio:.2f}"),
		("Number of Times Yosys Results Smaller", str(num_better)),
		("Number of Times Yosys Results Same", str(num_same)),
		("Number of Times Yosys Results Larger", str(num_worse)),
	]
	print_table("Results", items)

if __name__ == "__main__":
	main()
