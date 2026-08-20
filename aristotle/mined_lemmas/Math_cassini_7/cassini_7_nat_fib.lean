import Mathlib
import RequestProject.Cassini7

/-!
# Cassini 7, stated with Mathlib's Fibonacci numbers

Companion to `RequestProject/Cassini7.lean`.  Here the same identity
`F 6 * F 8 - F 7 ^ 2 = (-1) ^ 7` is stated for Mathlib's `Nat.fib` (and `Int.fib`), and the
`Int.fib` version is deduced from the general Mathlib lemma
`Int.fib_succ_mul_fib_pred_sub_fib_sq` (**Cassini's identity**).
-/

namespace Math

/-- The locally defined `Math.fib` agrees with Mathlib's `Nat.fib`. -/

theorem cassini_7_nat_fib :
    (Nat.fib 6 : ℤ) * (Nat.fib 8 : ℤ) - (Nat.fib 7 : ℤ) ^ 2 = (-1) ^ 7 := by
  have h := cassini_7_int_fib
  simp only [show ((8 : ℤ) = ((8 : ℕ) : ℤ)) from rfl, show ((6 : ℤ) = ((6 : ℕ) : ℤ)) from rfl,
    show ((7 : ℤ) = ((7 : ℕ) : ℤ)) from rfl, Int.fib_natCast] at h
  linarith [h]

end Math

/-!
# Cassini 7
Category: Pure Mathematics
Target: Math.cassini_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires every `import` command to occur at the very top of a
file, before any other syntax (including module doc comments such as the header above).
Since this file must *begin* with the header comment, it is kept import-free and therefore
self-contained: the Fibonacci sequence is defined here from scratch.  The companion file
`RequestProject/Cassini7Mathlib.lean` restates the same identity for Mathlib's `Nat.fib`
and `Int.fib`, and derives it from the general Mathlib lemma
`Int.fib_succ_mul_fib_pred_sub_fib_sq` (**Cassini's identity**).
-/

namespace Math

/-- The Fibonacci sequence: `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`. -/
