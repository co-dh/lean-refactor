namespace Fix.CL

theorem foo (n : Nat) : n = n := rfl

-- The same-file use `inspect` already found before the fix; kept so the regression test also
-- checks it is still found, not just the cross-file one below.
theorem baz (n : Nat) : n = n := foo n

end Fix.CL
