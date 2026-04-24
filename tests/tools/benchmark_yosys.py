#!/usr/bin/env python3
#
# Run repeatable Yosys command benchmarks and collect pass timing data.
#
# Examples:
#   python3 tests/tools/benchmark_yosys.py --yosys ./yosys --repeat 5
#   python3 tests/tools/benchmark_yosys.py --case opt=tests/opt/opt_share_large_pmux_cat.ys
#   python3 tests/tools/benchmark_yosys.py --case tiny="read_verilog tests/simple/multiplier.v; synth -noabc"

import argparse
import json
import os
from pathlib import Path
import re
import statistics
import subprocess
import sys
import tempfile
import time


REPO_ROOT = Path(__file__).resolve().parents[2]


DEFAULT_CASES = {
    "simple_synth_noabc": {
        "cwd": REPO_ROOT,
        "script": (
            "read_verilog tests/simple/aes_kexp128.v "
            "tests/simple/multiplier.v tests/simple/omsp_dbg_uart.v; "
            "hierarchy -auto-top; synth -noabc; stat"
        ),
    },
    "opt_share_large_pmux_cat": {
        "cwd": REPO_ROOT / "tests" / "opt",
        "script_file": REPO_ROOT / "tests" / "opt" / "opt_share_large_pmux_cat.ys",
    },
}


END_RE = re.compile(
    r"End of script\..*?time:\s+([0-9.]+)s,\s+user:\s+([0-9.]+)s,\s+system:\s+([0-9.]+)s"
)
PASS_RE = re.compile(r"^\s*([0-9]+)%\s+([0-9]+)\s+calls\s+([0-9.]+)\s+sec\s+(.+?)\s*$")


def parse_case(text):
    if "=" not in text:
        raise argparse.ArgumentTypeError("case must be NAME=SCRIPT_OR_FILE")
    name, spec = text.split("=", 1)
    name = name.strip()
    spec = spec.strip()
    if not name:
        raise argparse.ArgumentTypeError("case name must not be empty")

    path = Path(spec)
    if path.exists():
        path = path.resolve()
        return name, {"cwd": path.parent, "script_file": path}

    return name, {"cwd": REPO_ROOT, "script": spec}


def median(values):
    return statistics.median(values) if values else None


def stdev(values):
    if len(values) < 2:
        return 0.0
    return statistics.stdev(values)


def parse_yosys_output(output):
    end = END_RE.search(output)
    timings = {}

    for line in output.splitlines():
        match = PASS_RE.match(line)
        if match:
            pct, calls, seconds, name = match.groups()
            timings[name] = {
                "percent": int(pct),
                "calls": int(calls),
                "seconds": float(seconds),
            }

    return {
        "reported_wall_seconds": float(end.group(1)) if end else None,
        "reported_user_seconds": float(end.group(2)) if end else None,
        "reported_system_seconds": float(end.group(3)) if end else None,
        "pass_timings": timings,
    }


def run_case(yosys, case_name, case, keep_logs, out_dir):
    command = [str(yosys), "-Q", "-d"]
    temp_script = None

    if "script_file" in case:
        command += ["-s", str(case["script_file"])]
    else:
        temp_script = tempfile.NamedTemporaryFile("w", suffix=".ys", delete=False, encoding="utf-8")
        temp_script.write(case["script"])
        temp_script.close()
        command += ["-s", temp_script.name]

    started = time.perf_counter()
    proc = subprocess.run(
        command,
        cwd=case["cwd"],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    elapsed = time.perf_counter() - started

    output = proc.stdout
    if keep_logs:
        out_dir.mkdir(parents=True, exist_ok=True)
        log_path = out_dir / f"{case_name}.log"
        log_path.write_text(output, encoding="utf-8")
    else:
        log_path = None

    if temp_script is not None:
        os.unlink(temp_script.name)

    parsed = parse_yosys_output(output)
    parsed.update({
        "returncode": proc.returncode,
        "measured_wall_seconds": elapsed,
        "log": str(log_path) if log_path else None,
    })
    return parsed


def summarize_case(runs):
    ok_runs = [run for run in runs if run["returncode"] == 0]
    measured = [run["measured_wall_seconds"] for run in ok_runs]
    reported = [
        run["reported_wall_seconds"]
        for run in ok_runs
        if run["reported_wall_seconds"] is not None
    ]
    pass_names = sorted({
        name
        for run in ok_runs
        for name in run["pass_timings"].keys()
    })
    pass_summary = {}
    for name in pass_names:
        values = [
            run["pass_timings"][name]["seconds"]
            for run in ok_runs
            if name in run["pass_timings"]
        ]
        pass_summary[name] = {
            "median_seconds": median(values),
            "stdev_seconds": stdev(values),
            "samples": len(values),
        }

    return {
        "runs": len(runs),
        "ok_runs": len(ok_runs),
        "measured_wall_median_seconds": median(measured),
        "measured_wall_stdev_seconds": stdev(measured),
        "reported_wall_median_seconds": median(reported),
        "reported_wall_stdev_seconds": stdev(reported),
        "pass_timings": pass_summary,
    }


def print_table(results):
    print("\nCase                         ok/runs  measured median  reported median")
    print("---------------------------  -------  ---------------  ---------------")
    for name, data in results.items():
        summary = data["summary"]
        measured = summary["measured_wall_median_seconds"]
        reported = summary["reported_wall_median_seconds"]
        measured_s = "n/a" if measured is None else f"{measured:8.3f}s"
        reported_s = "n/a" if reported is None else f"{reported:8.3f}s"
        print(
            f"{name[:27]:27}  "
            f"{summary['ok_runs']:2}/{summary['runs']:<4}  "
            f"{measured_s:>15}  {reported_s:>15}"
        )

    print("\nTop median pass timings:")
    for name, data in results.items():
        summary = data["summary"]
        passes = [
            (pname, pdata["median_seconds"])
            for pname, pdata in summary["pass_timings"].items()
            if pdata["median_seconds"] is not None
        ]
        passes.sort(key=lambda item: item[1], reverse=True)
        top = ", ".join(f"{pname} {seconds:.3f}s" for pname, seconds in passes[:5])
        print(f"  {name}: {top or 'n/a'}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--yosys", default=str(REPO_ROOT / "yosys"), help="Yosys executable")
    parser.add_argument("--repeat", type=int, default=3, help="measured runs per case")
    parser.add_argument("--warmup", type=int, default=1, help="unrecorded warmup runs per case")
    parser.add_argument("--case", action="append", type=parse_case, help="NAME=SCRIPT_OR_FILE")
    parser.add_argument("--output", default="benchmark_yosys.json", help="JSON output path")
    parser.add_argument("--keep-logs", action="store_true", help="write per-run logs next to JSON")
    args = parser.parse_args()

    yosys = Path(args.yosys).resolve()
    if not yosys.exists() and yosys.suffix == "" and yosys.with_suffix(".exe").exists():
        yosys = yosys.with_suffix(".exe")
    if not yosys.exists():
        print(f"error: Yosys executable not found: {yosys}", file=sys.stderr)
        return 2

    cases = dict(DEFAULT_CASES)
    if args.case:
        cases = {name: case for name, case in args.case}

    out_path = Path(args.output).resolve()
    log_dir = out_path.with_suffix("")
    results = {}

    for name, case in cases.items():
        print(f"running {name}...")
        for _ in range(args.warmup):
            run_case(yosys, name, case, False, log_dir)

        runs = []
        for run_index in range(args.repeat):
            run_name = f"{name}.{run_index + 1}"
            runs.append(run_case(yosys, run_name, case, args.keep_logs, log_dir))

        results[name] = {
            "cwd": str(case["cwd"]),
            "script_file": str(case["script_file"]) if "script_file" in case else None,
            "script": case.get("script"),
            "runs": runs,
            "summary": summarize_case(runs),
        }

    report = {
        "yosys": str(yosys),
        "repeat": args.repeat,
        "warmup": args.warmup,
        "results": results,
    }
    out_path.write_text(json.dumps(report, indent=2, sort_keys=True), encoding="utf-8")
    print_table(results)
    print(f"\nwrote {out_path}")

    return 1 if any(run["returncode"] for data in results.values() for run in data["runs"]) else 0


if __name__ == "__main__":
    sys.exit(main())
