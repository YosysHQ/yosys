import sys
import pathlib
import subprocess

out = sys.argv[1]
files = sys.argv[2:]

final_archive_objects = []
custom_silimate_symbols = set()
for object in filter(lambda x: x.endswith(".o"), files):
	final_archive_objects.append(object)
	result = subprocess.check_output(["nm", "-gjU", object], encoding="utf8")
	custom_silimate_symbols.update(filter(lambda x: len(x.strip()), result.splitlines()))

symbol_localize_args = [f"-L{symbol}" for symbol in custom_silimate_symbols]

cwd = pathlib.Path(".").resolve()
for archive in filter(lambda x: x.endswith(".a"), files):
	file_path = pathlib.Path(archive)
	name = file_path.stem
	object_dir = cwd / "verific-merge" / name
	object_dir.mkdir(parents=True, exist_ok=True)
	subprocess.check_call(["ar", "x", archive], cwd=object_dir)
	for object in object_dir.glob("*"):
		if len(symbol_localize_args):
			subprocess.check_call(["objcopy", *symbol_localize_args, object])
		final_archive_objects.append(object)

subprocess.check_call(["ar", "rcs", out, *final_archive_objects])
