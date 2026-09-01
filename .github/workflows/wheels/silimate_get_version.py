import argparse
import subprocess
from pathlib import Path
from githubkit import GitHub
from githubkit.exception import RequestFailed

__file_dir__ = Path(__file__).absolute().parent
__yosys_root__ = __file_dir__.parents[2]

def get_wheel_version(repo_full_name, github_token):
	"""
	outputs wheel version according to silimate versioning strategy, which is

	{upstream major}.{upstream minor}.post{releases with this ver (elided if 0)}+sm
	"""
	major_minor_ver = subprocess.check_output([
		"cmake",
		f"-DYOSYS_CMAKE_SOURCE_DIR={__yosys_root__}",
		"-DYOSYS_VERSION_COMMIT=0",
		"-P",
		str(__yosys_root__ / "cmake/GetPyosysVersion.cmake"),
	], encoding="utf8").strip()

	gh = GitHub(github_token)
	owner_name, repo_name = repo_full_name.rsplit("/", maxsplit=1)

	post = 0
	final_release_tag = f"{major_minor_ver}+sm"
	last_tag_exists = True
	while last_tag_exists:
		last_tag_exists = False
		try:
			gh.rest.repos.get_release_by_tag(owner_name, repo_name, f"v{final_release_tag}")
			last_tag_exists = True
			post += 1
			final_release_tag = f"{major_minor_ver}.post{post}+sm"
		except RequestFailed as e:
			if e.response.status_code == 404:
				break
			else:
				raise e from None

	print(final_release_tag, end="")

if __name__ == "__main__":
	ap = argparse.ArgumentParser()
	ap.add_argument("--github-token")
	ap.add_argument("repo_full_name")
	ns = ap.parse_args()
	get_wheel_version(**ns.__dict__)
