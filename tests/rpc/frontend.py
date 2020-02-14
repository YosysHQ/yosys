def modules():
	return ["python_inv"]

def derive(module, parameters):
	assert module == r"python_inv"
	if parameters.keys() != {r"\width"}:
		raise ValueError("Invalid parameters")
	return "ilang", r"""
module \impl
	wire width {width:d} input 1 \i
	wire width {width:d} output 2 \o
	cell $neg $0
		parameter \A_SIGNED 1'0
		parameter \A_WIDTH 32'{width:b}
		parameter \Y_WIDTH 32'{width:b}
		connect \A \i
		connect \Y \o
	end
end
module \python_inv
	wire width {width:d} input 1 \i
	wire width {width:d} output 2 \o
	cell \impl $0
		connect \i \i
		connect \o \o
	end
end
""".format(width=parameters[r"\width"])

# ----------------------------------------------------------------------------

import json
import argparse
import sys, socket, os, subprocess
try:
	import msvcrt, win32pipe, win32file
except ImportError:
	msvcrt = win32pipe = win32file = None

def map_parameter(parameter):
	if parameter["type"] == "unsigned":
		return int(parameter["value"], 2)
	if parameter["type"] == "signed":
		width = len(parameter["value"])
		value = int(parameter["value"], 2)
		if value & (1 << (width - 1)):
			value = -((1 << width) - value)
		return value
	if parameter["type"] == "string":
		return parameter["value"]
	if parameter["type"] == "real":
		return float(parameter["value"])

def call(input_json):
	input = json.loads(input_json)
	if input["method"] == "modules":
		return json.dumps({"modules": modules()})
	if input["method"] == "derive":
		try:
			frontend, source = derive(input["module"],
				{name: map_parameter(value) for name, value in input["parameters"].items()})
			return json.dumps({"frontend": frontend, "source": source})
		except ValueError as e:
			return json.dumps({"error": str(e)})

def main():
	parser = argparse.ArgumentParser()
	modes = parser.add_subparsers(dest="mode")
	mode_stdio = modes.add_parser("stdio")
	if os.name == "posix":
		mode_path = modes.add_parser("unix-socket")
	if os.name == "nt":
		mode_path = modes.add_parser("named-pipe")
	mode_path.add_argument("path")
	args = parser.parse_args()

	if args.mode == "stdio":
		while True:
			input = sys.stdin.readline()
			if not input: break
			sys.stdout.write(call(input) + "\n")
			sys.stdout.flush()

	if args.mode == "unix-socket":
		sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
		sock.bind(args.path)
		try:
			ys_proc = subprocess.Popen(["../../yosys", "-ql", "unix.log", "-p", "connect_rpc -path {}; read_verilog design.v; hierarchy -top top; flatten; select -assert-count 1 t:$neg".format(args.path)])
			sock.listen(1)
			conn, addr = sock.accept()
			file = conn.makefile("rw")
			while True:
				input = file.readline()
				if not input: break
				file.write(call(input) + "\n")
				file.flush()
			ys_proc.wait(timeout=10)
			if ys_proc.returncode:
				raise subprocess.CalledProcessError(ys_proc.returncode, ys_proc.args)
		finally:
			ys_proc.kill()
			sock.close()
			os.unlink(args.path)

	if args.mode == "named-pipe":
		pipe = win32pipe.CreateNamedPipe(args.path, win32pipe.PIPE_ACCESS_DUPLEX,
		    win32pipe.PIPE_TYPE_BYTE|win32pipe.PIPE_READMODE_BYTE|win32pipe.PIPE_WAIT,
		    1, 4096, 4096, 0, None)
		win32pipe.ConnectNamedPipe(pipe, None)
		try:
			while True:
				input = b""
				while not input.endswith(b"\n"):
					result, data = win32file.ReadFile(pipe, 4096)
					assert result == 0
					input += data
					assert not b"\n" in input or input.endswith(b"\n")
				output = (call(input.decode("utf-8")) + "\n").encode("utf-8")
				length = len(output)
				while length > 0:
					result, done = win32file.WriteFile(pipe, output)
					assert result == 0
					length -= done
		except win32file.error as e:
			if e.args[0] == 109: # ERROR_BROKEN_PIPE
				pass
			else:
				raise

if __name__ == "__main__":
	main()
