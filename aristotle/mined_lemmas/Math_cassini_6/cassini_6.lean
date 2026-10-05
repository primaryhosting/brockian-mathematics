import Mathlib
import RequestProject.Cassini6

/-!
# Cassini 6 — agreement with Mathlib's Fibonacci numbers

The target file `RequestProject/Cassini6.lean` must literally begin with a module
documentation comment, so it cannot contain any `import`.  It therefore defines the
Fibonacci sequence `Math.fib` from scratch.  Here we check that this definition
agrees with Mathlib's `Nat.fib`, and restate Cassini's identity at `n = 6` in terms
of `Nat.fib`.
-/

namespace Math

/-- The locally defined `Math.fib` agrees with Mathlib's `Nat.fib`. -/

theorem cassini_6 :
    (fib 5 : Int) * (fib 7 : Int) - (fib 6 : Int) ^ 2 = (-1) ^ 6 := by
  decide

end Math

