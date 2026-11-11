#!/bin/sh
# test-rename-position.sh — regression test for `lean-refactor rename --terms-only` / `--patterns-only`.
#
# `scripts/fixtures/rename-position`: the `@[match_pattern]` def `Shape.gen` is used in terms (an
# application, a list element, a `.gen`, a `fun` alternative's right-hand side) and in patterns (an
# equation-style definition, a `fun` alternative, a `match` with `.gen`, an `if let`).  `--terms-only`
# moves the terms and leaves every pattern; `--patterns-only` the mirror.  The new name must not exist
# (rename's own check), so the selection is read off the preview, which writes nothing.
#
# Builds the fixture in a scratch copy (so `.lake` never lands in the checked-in fixture).
set -e
root=$(dirname "$(dirname "$(readlink -f "$0")")")
work=$(mktemp -d "${TMPDIR:-/tmp}/test-rename-position.XXXXXX")
trap 'rm -rf "$work"' EXIT
cp -r "$root/scripts/fixtures/rename-position"/. "$work"/
cd "$work"
"$root/scripts/cap" lake build -q Fix
original=$(cat Fix/Use.lean)
terms=$("$root/scripts/lean-refactor" rename Shape.gen Shape.mk1 --terms-only --no-index --in Fix/Use.lean)
echo "$terms"
patterns=$("$root/scripts/lean-refactor" rename Shape.gen Shape.gen3 --patterns-only --no-index --in Fix/Use.lean)
echo "$patterns"
[ "$(cat Fix/Use.lean)" = "$original" ] || { echo "test-rename-position: a preview wrote Fix/Use.lean"; exit 1; }
set +e
both=$("$root/scripts/lean-refactor" rename Shape.gen Shape.mk1 --terms-only --patterns-only 2>&1)
set -e

fail=0
check() {
  case "$1" in
    *"$2"*) ;;
    *) echo "test-rename-position: MISSING \`$2\`"; fail=1 ;;
  esac
}
absent() {
  case "$1" in
    *"$2"*) echo "test-rename-position: UNEXPECTED \`$2\`"; fail=1 ;;
  esac
}
check "$terms" 'Fix/Use.lean: 4 use(s) in term position, 4 in pattern position'
check "$terms" 'Fix/Use.lean:4: "Shape.gen" -> "Shape.mk1"'
check "$terms" 'Fix/Use.lean:5: "gen" -> "mk1"'
check "$terms" 'Fix/Use.lean:5: ".gen" -> ".mk1"'
check "$terms" 'Fix/Use.lean:10: "gen" -> "mk1"'
absent "$terms" 'Fix/Use.lean:7:'
absent "$terms" 'Fix/Use.lean:10: "Shape.gen"'
absent "$terms" 'Fix/Use.lean:13:'
absent "$terms" 'Fix/Use.lean:15:'
check "$patterns" 'Fix/Use.lean:7: "gen" -> "gen3"'
check "$patterns" 'Fix/Use.lean:10: "Shape.gen" -> "Shape.gen3"'
check "$patterns" 'Fix/Use.lean:13: ".gen" -> ".gen3"'
check "$patterns" 'Fix/Use.lean:15: "gen" -> "gen3"'
absent "$patterns" 'Fix/Use.lean:4:'
absent "$patterns" 'Fix/Use.lean:5:'
absent "$patterns" 'Fix/Use.lean:10: "gen"'
check "$both" '--terms-only and --patterns-only select disjoint uses; pass one'

if [ "$fail" = 0 ]; then echo "test-rename-position: PASS"; else echo "test-rename-position: FAIL"; exit 1; fi
