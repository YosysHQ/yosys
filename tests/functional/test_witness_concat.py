import json
import subprocess
import sys
from pathlib import Path

import pytest


@pytest.mark.parametrize("steps", [1, 2])
@pytest.mark.parametrize("input_width", [0, 3])
def test_concat_initial_state(tmp_path, steps, input_width):
    """Only the first output step should carry initialization-only bits."""
    signals = []
    if input_width:
        signals.append(dict(path=["\\input"], width=input_width,
                            offset=0, init_only=False))
    signals.append(dict(path=["\\state"], width=2,
                        offset=0, init_only=True))
    inputs = []
    for index in range(2):
        trace = dict(format="Yosys Witness Trace", clocks=[], signals=signals,
                     steps=[dict(bits="10" + "1" * input_width)] +
                           [dict(bits="0" * input_width)] * (steps - 1))
        path = tmp_path / f"input{index}.yw"
        path.write_text(json.dumps(trace))
        inputs.append(str(path))
    output = tmp_path / "joined.yw"
    witness = Path(__file__).resolve().parents[2] / "backends/smt2/witness.py"
    result = subprocess.run([sys.executable, str(witness), "yw2yw",
                             *inputs, str(output)], capture_output=True, text=True)
    assert result.returncode == 0, result.stdout + result.stderr
    joined = json.loads(output.read_text())
    assert [step["bits"] for step in joined["steps"]] == (
        ["10" + "1" * input_width] + ["0" * input_width] * (steps - 1) +
        ["1" * input_width] + ["0" * input_width] * (steps - 1))
    assert result.stdout.count(f"copied {steps} time steps.") == 2
