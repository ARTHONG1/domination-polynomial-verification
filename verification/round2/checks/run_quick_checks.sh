#!/bin/sh
# Re-runs the quick checks of verification round 2 and compares the results
# with the committed output. Needs a C++17 compiler and Python >= 3.10.
# Run from anywhere inside a git clone of the repository.
set -eu
cd "$(dirname "$0")"
CXX=${CXX:-c++}
PY=${PYTHON:-python3}
B=$(mktemp -d)

$CXX -O3 -std=c++17 sec2_4_labelled_census.cpp -o "$B/sec2_4"
"$B/sec2_4" > SEC2_4_LABELLED_CENSUS.json 2> SEC2_4_LABELLED_CENSUS.log
$CXX -O3 -std=c++17 u_bruteforce_2pow27.cpp -o "$B/u_bruteforce"
"$B/u_bruteforce" > U_BRUTEFORCE.json

$PY table_counts.py > TABLE_COUNTS.json
$PY narrative_arithmetic.py
$PY component_product.py > COMPONENT_PRODUCT.json
$PY u_figure_isomorphism.py > /dev/null
$PY remark_6_4_boundary_forests.py > /dev/null
$PY prop_7_2_exact.py > /dev/null
$PY sec7_jump_census.py > /dev/null
$PY definition_checks.py > /dev/null
$PY identity_checks.py > /dev/null
$PY family_remark_6_8.py
$PY dp_semantics.py | tail -1

git diff --exit-code -- .
echo "All quick checks reproduced the committed output."
