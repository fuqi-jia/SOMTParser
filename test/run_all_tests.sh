#!/usr/bin/env bash
set -euo pipefail

PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BUILD_DIR="${SOMTPARSER_BUILD_DIR:-${PROJECT_ROOT}/build}"

# Include the optional PDDL and semantic-check helpers. The convert API and its
# tests belong to the language library and do not require tools to be enabled.
cmake -S "${PROJECT_ROOT}" -B "${BUILD_DIR}" \
  -DCMAKE_BUILD_TYPE="${CMAKE_BUILD_TYPE:-Debug}" \
  -DSOMTPARSER_WARNINGS_AS_ERRORS="${SOMTPARSER_WARNINGS_AS_ERRORS:-ON}" \
  -DSOMTPARSER_BUILD_TESTS=ON \
  -DSOMTPARSER_BUILD_TOOLS=ON
# Bare `--parallel` uses every core, which is right on a CI runner and wrong on a
# memory-constrained WSL2 box -- a full-core build of this tree took one down mid-run.
# SOMTPARSER_BUILD_JOBS caps both phases; unset reproduces the previous behaviour
# exactly, so CI is unaffected.
JOBS="${SOMTPARSER_BUILD_JOBS:-}"
cmake --build "${BUILD_DIR}" --parallel ${JOBS}
ctest --test-dir "${BUILD_DIR}" --output-on-failure ${JOBS:+-j ${JOBS}}
