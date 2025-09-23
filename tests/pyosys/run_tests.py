import sys
import shutil
import shlex
import subprocess
from pathlib import Path

__file_dir__ = Path(__file__).absolute().parent

if len(sys.argv) > 2 or len(sys.argv) == 2 and sys.argv[1] != 'yosys':
	print(f"Usage: {sys.argv[0]} [yosys]")
	exit(64)

if len(sys.argv) == 2:
	binary = [str(__file_dir__.parents[1] / "yosys"), "-Qy"]
else:
	binary = [sys.executable or shutil.which("python3") or "python3"] # sys.executable can actually be None

tests = __file_dir__.glob("test_*.py")

log_dir = __file_dir__ / "logs"
try:
	shutil.rmtree(log_dir)
except FileNotFoundError:
	pass
fail_logs = set()
for test in tests:
	print(f"* {test.name} ", end="")
	log_dir.mkdir(parents=True, exist_ok=True)
	log = log_dir / (test.stem + ".log")
	cmd = [*binary, str(test)]
	log_file = open(log, "w", encoding="utf8")
	log_file.write(f"$ {shlex.join(cmd)}\n")
	log_file.flush()
	result = subprocess.run(cmd, stdout=log_file, stderr=subprocess.STDOUT)
	if result.returncode == 0:
		print("OK!")
	else:
		print(f"FAILED: {log}")
		fail_logs.add(log)
	log_file.close()
for log in fail_logs:
	print(f">>> {log}")
	with open(log, encoding="utf8") as f:
		print(f.read())
if len(fail_logs):
	exit(1)
