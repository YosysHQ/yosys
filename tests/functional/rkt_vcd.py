from __future__ import annotations
from pathlib import Path
import re
import subprocess
from typing import Dict, List, Tuple
from random import Random

vcd_version = "Yosys/tests/functional/rkt_vcd.py"
StepList = List[Tuple[int, str]]
SignalStepMap = Dict[str, StepList]
SignalWidthMap = Dict[str, int]

def write_vcd(filename: Path, signals: SignalStepMap, timescale='1 ns', date='today'):
    with open(filename, 'w') as f:
        # Write the header
        f.write(f"$date\n    {date}\n$end\n")
        f.write(f"$timescale {timescale} $end\n")
        
        # Declare signals
        f.write("$scope module gold $end\n")
        for signal_name, changes in signals.items():
            signal_size = len(changes[0][1])
            f.write(f"$var wire {signal_size - 1} {signal_name} {signal_name} $end\n")
        f.write("$upscope $end\n")
        f.write("$enddefinitions $end\n")
        
        # Collect all unique timestamps
        timestamps = sorted(set(time for changes in signals.values() for time, _ in changes))
        
        # Write initial values
        f.write("#0\n")
        for signal_name, changes in signals.items():
            for time, value in changes:
                if time == 0:
                    f.write(f"{value} {signal_name}\n")
        
        # Write value changes
        for time in timestamps:
            if time != 0:
                f.write(f"#{time}\n")
                for signal_name, changes in signals.items():
                    for change_time, value in changes:
                        if change_time == time:
                            f.write(f"{value} {signal_name}\n")

def simulate_rosette(rkt_file_path: Path, vcd_path: Path, num_steps: int, rnd: Random):
    signals: dict[str, list[str]] = {}
    inputs: SignalWidthMap = {}
    outputs: SignalWidthMap = {}

    current_struct_name: str = ""
    with open(rkt_file_path, 'r') as rkt_file:
        for line in rkt_file:
            m = re.search(r'gold_(Inputs|Outputs|State)', line)
            if m:
                current_struct_name = m.group(1)
                if current_struct_name == "State": break
            elif not current_struct_name: continue # skip lines before structs
            m = re.search(r'; (.+?)\b \(bitvector (\d+)\)', line)
            if not m: continue # skip non matching lines (probably closing the struct)
            signal = m.group(1)
            width = int(m.group(2))
            if current_struct_name == "Inputs":
                inputs[signal] = width
            elif current_struct_name == "Outputs":
                outputs[signal] = width

    for signal, width in inputs.items():
        step_list: list[int] = []
        for step in range(num_steps):
            value = rnd.getrandbits(width)
            binary_string = format(value, '0{}b'.format(width))
            step_list.append(binary_string)
        signals[signal] = step_list

    test_rkt_file_path = rkt_file_path.with_suffix('.tst.rkt')
    with open(test_rkt_file_path, 'w') as test_rkt_file:
        test_rkt_file.writelines([
            '#lang rosette\n',
            f'(require "{rkt_file_path.name}")\n',
        ])

        for step in range(num_steps):
            this_step = f"step_{step}"
            value_list: list[str] = []
            for signal, width in inputs.items():
                value = signals[signal][step]
                value_list.append(f"(bv #b{value} {width})")
            gold_Inputs = f"(gold_Inputs {' '.join(value_list)})"
            gold_State = f"(cdr step_{step-1})" if step else "gold_initial"
            test_rkt_file.write(f"(define {this_step} (gold {gold_Inputs} {gold_State})) (car {this_step})\n")

    cmd = ["racket", test_rkt_file_path]
    status = subprocess.run(cmd, capture_output=True)
    assert status.returncode == 0, f"{cmd[0]} failed"

    for signal in outputs.keys():
        signals[signal] = []

    for line in status.stdout.decode().splitlines():
        m = re.match(r'\(gold_Outputs( \(bv \S+ \d+\))+\)', line)
        assert m, f"Incomplete output definition {line!r}"
        for output, (value, width) in zip(outputs.keys(), re.findall(r'\(bv (\S+) (\d+)\)', line)):
            assert isinstance(value, str), f"Bad value {value!r}"
            assert value.startswith(('#b', '#x')), f"Non-binary value {value!r}"
            assert int(width) == outputs[output], f"Width mismatch for output {output!r} (got {width}, expected {outputs[output]})"
            int_value = int(value[2:], 16 if value.startswith('#x') else 2)
            binary_string = format(int_value, '0{}b'.format(width))
            signals[output].append(binary_string)

    vcd_signals: SignalStepMap = {}
    for signal, steps in signals.items():
        vcd_signals[signal] = [(time, f"b{value}") for time, value in enumerate(steps)]

    write_vcd(vcd_path, vcd_signals)
