#!/bin/sh
# test-inspect.sh — regression test for `lean-refactor inspect`: a call site reached through an
# `open`ed SIBLING namespace must be reported, not just uses in the file that declares the name.
#
# `scripts/fixtures/inspect-sibling-ns` reproduces the shape that hid three of freyd's five real
# call sites of `RelSet.CL.est_pt` (freyd commit 83c2f5d, fixed at c8c300d): `Fix/Base.lean` declares
# `Fix.CL.foo` under `namespace Fix.CL` and uses it once itself (`Fix.CL.baz`); `Fix/Other.lean` is a
# SEPARATE file, in the sibling namespace `Fix.GD`, that reaches `foo` only through `open Fix.CL`
# (`Fix.GD.bar`).  The bug: `inspect` elaborated only the file that DECLARES the name and looked at
# just that file's `.ilean`, so `Fix.Other`'s use was silently absent even though the index's
# `use_site` table already had it (Lean's own reference tracking resolves `open` correctly — nothing
# populating that table was ever missing anything). The fix makes `inspect` check every file the
# index recorded a use in, not only the declaring one.
#
# Builds the fixture in a scratch copy (so `.lake` never lands in the checked-in fixture), indexes
# it, and checks BOTH sites are found.
set -e
root=$(dirname "$(dirname "$(readlink -f "$0")")")
fixture="$root/scripts/fixtures/inspect-sibling-ns"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
cp -r "$fixture"/. "$work"/
cd "$work"
"$root/scripts/cap" lake build -q
"$root/scripts/lean-refactor" index --full >/dev/null
out=$("$root/scripts/lean-refactor" inspect Fix.CL.foo)
echo "$out"

fail=0
for needle in \
  "Fix.CL.foo: 1 resolved use(s) in Fix.Base" \
  "Fix.CL.foo: 1 resolved use(s) in Fix.Other" \
  "Fix.CL.baz" \
  "Fix.GD.bar"
do
  case "$out" in
    *"$needle"*) ;;
    *) echo "test-inspect: MISSING \`$needle\`"; fail=1 ;;
  esac
done

if [ "$fail" = 0 ]; then
  echo "test-inspect: PASS"
else
  echo "test-inspect: FAIL"
  exit 1
fi
