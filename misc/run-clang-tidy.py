#!/usr/bin/env python3

import sys

from argparse           import ArgumentParser, ArgumentDefaultsHelpFormatter
from pathlib            import Path
from subprocess         import run
from concurrent.futures import ThreadPoolExecutor

def main() -> int:
	parser = ArgumentParser(
		formatter_class = ArgumentDefaultsHelpFormatter,
		description     = 'clang-tidy runner',
		prog            = 'run-clang-tidy.py',
	)

	parser.add_argument(
		'--source-path', '-s',
		required = True,
		type     = Path,
		metavar  = 'source_path',
		help     = 'Path to the source directory to run clang-tidy in'
	)

	parser.add_argument(
		'--build-path', '-p',
		required = True,
		type     = Path,
		metavar  = 'build_path',
		help     = 'Path to the build directory containing a compile_commands.json'
	)

	args = parser.parse_args()

	def glob_files():
		paths    = {'backends', 'frontend', 'kernel', 'passes', 'techlibs'}
		suffixes = {'cc', 'h'}

		for path in paths:
			for suffix in suffixes:
				yield args.source_path.glob(f'{path}/**/*.{suffix}')

	def gather_files():
		for file_glob in glob_files():
			for file in file_glob:
				yield file

	extra_args = ()
	futures = []

	with ThreadPoolExecutor() as pool:
		for file in gather_files():
			futures.append(pool.submit(
				run, ['clang-tidy', *extra_args, '-p', args.build_path, file]
			))

	return max((future.result().returncode for future in futures))


if __name__ == '__main__':
	sys.exit(main())
