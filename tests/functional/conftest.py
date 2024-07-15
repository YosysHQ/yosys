import pytest
from rtlil_cells import generate_test_cases

def pytest_addoption(parser):
    parser.addoption(
        "--per-cell", type=int, default=None, help="run only N tests per cell"
    )

def pytest_generate_tests(metafunc):
    if "cell" in metafunc.fixturenames:
        print(dir(metafunc.config))
        per_cell = metafunc.config.getoption("per_cell", default=None)
        names, cases = generate_test_cases(per_cell)
        metafunc.parametrize("cell,parameters", cases, ids=names)