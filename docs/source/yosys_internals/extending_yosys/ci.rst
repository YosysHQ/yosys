Continuous Integration
======================

.. seealso:: Information about test suites is covered in :doc:`test_suites`

- combination of public (github) runners and private runner (for building with
  Verific)

Manually triggering jobs
------------------------

- most jobs can run on ``workflow_dispatch``, allowing manual starting of a job
  on any branch
- jobs which run on a public (github) runner can generally be run on any fork of
  the repo
- `learn more about GitHub Actions
  <https://docs.github.com/en/actions/get-started>`_

Workflows
---------

- located in :file:`.github/workflows`
- most jobs will be cancelled if a newer commit is pushed, prioritizing the most
  up-to-date version instead

  - jobs running on the main branch will never be cancelled

- most jobs will skip documentation-only changes (:file:`docs` directory and
  readme file)

Compiler testing
~~~~~~~~~~~~~~~~

- ``test-compile.yml``
- most of these use ``make compile-only``, meaning no linking (or executing)
- run on pushes to main and PRs

- gcc

  - oldest supported
  - newest supported

- clang

  - latest ubuntu, oldest supported
  - latest ubuntu, newest supported
  - macOS x86
  - macOS arm
  - verific configurations (``test-verific-cfg.yml``
    manually triggered only)

- C++17
- C++20 (newest compiler versions only)

Build testing
~~~~~~~~~~~~~

- ``test-build.yml``

  - run on pushes to main and PRs
  - builds once (per OS) out-of-tree, using the same build artifact across tests
  - mostly covered by :doc:`test_suites`
  - ``make``
  - ``make unit-test``
  - ``make vanilla-test``
  - ``make -C docs test``

- ``test-sanitizers.yml``

  - uses private runner
  - run on pushes to main and during PR merges
  - ``make vanilla-test`` with ``SANITIZER=undefined,address``


Automatic testing with Verific
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

- ``test-verific.yml``
- uses private runner
- run on pushes to main and during PR merges
- build and test Yosys+Verific

  - Vanilla tests
  - Functional tests
  - SBY tests (using latest version of SBY)
  - Yosys+Verific specific tests

- also builds pyosys and runs pyosys tests

Extra build flows
~~~~~~~~~~~~~~~~~

- compiled and linked but not executed
- ``extra-builds.yml``

  - run on pushes to main and PRs
  - WASI (smoke test for YoWASP)
  - VS (not released, not maintained?)
  - nix (flake no longer updating, not maintained?)

- ``wheels.yml``

  - run once per week on latest main:
  - python wheels for PyPI release (pyosys)

Building documentation
~~~~~~~~~~~~~~~~~~~~~~

- uses private runner
- runs even on documentation-only changes, but still skips readme-only changes
- ``prepare-docs.yml``

  - run on all pushes and PRs
  - prepare docs artifact from Yosys executable (``make docs/prep``)
  - triggers ReadtheDocs build for main (latest), tagged versions (releases),
    and certain WIP doc previews

- ``test-build.yml``

  - run on pushes to main and PRs
  - ``make docs``, building both html and latexpdf targets (independently)

    - will fail on warnings to replicate ReadtheDocs behavior (which itself was
      configured to prevent updating live documentation with an incomplete or
      missing artifact)

CodeQL
~~~~~~

- ``codeql.yml``
- static code analysis
- run every day on latest main

Vendor sources
~~~~~~~~~~~~~~

- ``source-vendor.yml``
- download and package source code with all submodules
- used for releases (``yosys.tar.gz``)
- run on pushes to YosysHQ/yosys


Composite actions
-----------------

- consolidate common setup steps
- :file:`.github/actions/setup-build-env/action.yml`

  - consistent build environment setup
  - broken into build/docs/test dependencies (currently only on linux)

- :file:`.github/actions/setup-iverilog/action.yml`
  - iverilog install (including dependencies)
