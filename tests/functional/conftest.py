import pytest
from rtlil_cells import generate_test_cases
import random

random_seed = random.getrandbits(32)

def pytest_configure(config):
    config.addinivalue_line("markers", "smt: test uses smtlib/z3")
    config.addinivalue_line("markers", "rkt: test uses racket/rosette")

def pytest_addoption(parser):
    parser.addoption("--per-cell", type=int, default=None, help="run only N tests per cell")
    parser.addoption("--steps", type=int, default=1000, help="run each test for N steps")
    parser.addoption("--seed", type=int, default=random_seed, help="seed for random number generation, use random seed if unspecified")

def pytest_collection_finish(session):
    print('random seed: {}'.format(session.config.getoption("seed")))

@pytest.fixture
def num_steps(request):
    return request.config.getoption("steps")

@pytest.fixture
def rnd(request):
    seed1 = request.config.getoption("seed")
    return lambda seed2: random.Random('{}-{}'.format(seed1, seed2))

def pytest_generate_tests(metafunc):
    if "cell" in metafunc.fixturenames:
        per_cell = metafunc.config.getoption("per_cell", default=None)
        seed1 = metafunc.config.getoption("seed")
        rnd = lambda seed2: random.Random('{}-{}'.format(seed1, seed2))
        names, cases = generate_test_cases(per_cell, rnd)
        metafunc.parametrize("cell,parameters", cases, ids=names)
