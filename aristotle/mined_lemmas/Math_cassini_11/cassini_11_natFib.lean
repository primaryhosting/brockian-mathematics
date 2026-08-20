/-!
# Cassini 11
Category: Pure Mathematics
Target: Math.cassini_11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires `import` commands to be the very first commands of a
file, and a module docstring `/-! ... -/` counts as a command. Since the header comment above
must appear at the top of this file verbatim, this module is written without imports, using
its own definition of the Fibonacci sequence. The companion file
`RequestProject/Cassini11Mathlib.lean` imports Mathlib, proves that this definition agrees
with `Nat.fib`, and re-derives the same statement from Mathlib's general Cassini identity
`Int.fib_succ_mul_fib_pred_sub_fib_sq`.
-/

namespace Math

/-- The Fibonacci sequence: `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`. -/

theorem cassini_11_natFib :
    (Nat.fib 10 : ℤ) * (Nat.fib 12 : ℤ) - (Nat.fib 11 : ℤ) ^ 2 = (-1) ^ 11 := by
  have h := Int.fib_succ_mul_fib_pred_sub_fib_sq 11
  rw [show ((11:ℤ) + 1) = ((12:ℕ):ℤ) by norm_num, show ((11:ℤ) - 1) = ((10:ℕ):ℤ) by norm_num,
    show (11:ℤ) = ((11:ℕ):ℤ) by norm_num, Int.fib_natCast, Int.fib_natCast, Int.fib_natCast] at h
  rw [show ((11:ℕ):ℤ).natAbs = 11 from rfl] at h
  linarith [h]

/-- The statement of `Math.cassini_11` transported to Mathlib's `Nat.fib`. -/
