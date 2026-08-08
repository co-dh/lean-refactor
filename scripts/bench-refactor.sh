#!/bin/sh
# bench-refactor — wall-clock and peak-RSS of one `lean-refactor` invocation, one line per run.
#
# Usage: scripts/bench-refactor.sh <label> <lean-refactor args...>
# Prints: "<label>\t<seconds>\t<peak-rss-KB>\t<exit>"
label=$1
shift
start=$(date +%s%N)
out=$("$(dirname "$0")/lean-refactor" "$@" 2>&1)
code=$?
end=$(date +%s%N)
printf '%s\t%d.%03d\t%d\n' "$label" $(( (end - start) / 1000000000 )) \
  $(( ((end - start) / 1000000) % 1000 )) "$code"
[ -n "$BENCH_SHOW_OUTPUT" ] && printf '%s\n' "$out"
exit 0
