#!/bin/sh
# Runs both programs for the orders 2..MAX and cross-checks them.
# Usage: ./run_all.sh MAX [PROCESSES]     (MAX <= 27; PROCESSES is used for orders >= 23)
set -e
MAX="${1:-22}"; P="${2:-4}"
CXX="${CXX:-c++}"
mkdir -p bin logs results
$CXX -O3 -std=c++17 -Wall -Wextra -o bin/independent_check independent_check.cpp
$CXX -O3 -std=c++17 -Wall -Wextra -o bin/wrom_check wrom_check.cpp
$CXX -O3 -std=c++17 -Wall -Wextra -o bin/bruteforce_tree bruteforce_tree.cpp
n=2
while [ "$n" -le "$MAX" ]; do
  if [ "$n" -le 22 ]; then
    bin/independent_check "$n" "$n" 16 > "results/program1_order_$(printf %02d "$n").jsonl"
    bin/wrom_check "$n" "$n" > "results/program2_order_$(printf %02d "$n").jsonl"
  else
    r=0
    while [ "$r" -lt "$P" ]; do
      bin/independent_check "$n" "$n" 0 "$P" "$r" > "logs/extended_${n}_part${r}.jsonl" 2> "logs/extended_${n}_part${r}.stderr" &
      r=$((r+1))
    done
    bin/wrom_check "$n" "$n" > "logs/wrom_${n}.jsonl" 2> "logs/wrom_${n}.stderr" &
    wait
  fi
  echo "order $n done"
  n=$((n+1))
done
if [ "$MAX" -ge 23 ]; then python3 collect.py "$MAX"; fi
python3 cross_check.py "$MAX"
if [ "$MAX" -ge 22 ]; then python3 analyze.py; fi

