/-!
# Cassini 13
Category: Pure Mathematics
Target: Math.cassini_13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires `import` commands to be the very first
commands in a file, so no `import Mathlib` can appear after the header comment
above.  This file is therefore self-contained (it needs nothing beyond core
Lean).  The companion file `RequestProject/CassiniMathlib.lean` imports Mathlib
and re-derives the same identity for Mathlib's `Nat.fib`, together with the
proof that `Math.fib` agrees with `Nat.fib`.
-/

namespace Math

/-- The Fibonacci sequence: `fib 0 = 0`, `fib 1 = 1`,
`fib (n+2) = fib n + fib (n+1)`. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- Cassini's identity at `n = 13`: `F(12)·F(14) − F(13)² = (−1)^13`. -/
theorem cassini_13 :
    (fib 12 : Int) * (fib 14 : Int) - (fib 13 : Int) ^ 2 = (-1 : Int) ^ 13 := by
  decide

end Math

import Mathlib
import RequestProject.Main

/-!
# Cassini's identity at `n = 13`, stated with Mathlib's `Nat.fib`

This companion file connects `Math.fib` with Mathlib's `Nat.fib` and states the
general Cassini identity specialised at `n = 13`.
-/

namespace Math

/-- `Math.fib` agrees with Mathlib's `Nat.fib`. -/
theorem fib_eq_nat_fib : ∀ n, fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [fib, Nat.fib_add_two, fib_eq_nat_fib n, fib_eq_nat_fib (n + 1)]

/-- Cassini's identity at `n = 13` for Mathlib's `Nat.fib`:
`F(12)·F(14) − F(13)² = (−1)^13`. -/
theorem cassini_13_nat_fib :
    (Nat.fib 12 : ℤ) * (Nat.fib 14 : ℤ) - (Nat.fib 13 : ℤ) ^ 2 = (-1 : ℤ) ^ 13 := by
  simp only [← fib_eq_nat_fib]
  exact cassini_13

end Math

