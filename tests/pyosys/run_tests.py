from pathlib import Path
import shutil
import subprocess
import sys

__file_dir__ = Path(__file__).absolute().parent

if len(sys.argv) != 2:
	print(f"Usage: {sys.argv[0]} {sys.argv[1]}")
	exit(64)

binary = []
if sys.argv[1] in ["yosys"]:
	binary = [__file_dir__.parents[1] / "yosys", "-Qy"]
else:
	binary = [sys.argv[1]]

tests = __file_dir__.glob("test_*.py")
errors = False
log_dir = __file_dir__ / "logs"
try:
	shutil.rmtree(log_dir)
except FileNotFoundError:
	pass
for test in tests:
	print(f"* {test.name} ", end="")
	log_dir.mkdir(parents=True, exist_ok=True)
	log = log_dir / (test.stem + ".log")
	result = subprocess.run([
		*binary,
		test
	], stdout=open(log, "w"), stderr=subprocess.STDOUT)
	if result.returncode == 0:
		print("OK!")
	else:
		print(f"FAILED: {log}")
		errors = True
if errors:
	exit(1)
