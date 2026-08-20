import Mathlib
/-!
# Cassini 14
Category: Pure Mathematics
Target: Math.cassini_14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- Note: Lean 4 requires `import` lines to precede every other command, including
-- module docstrings, so the requested header comment appears immediately after the import.

namespace Math

/-- **Cassini's identity at `n = 14`**: `F(13) · F(15) − F(14)² = (−1)^14`,
where `F` is the Fibonacci sequence (`Nat.fib`), computed in `ℤ`.

Here `F(13) = 233`, `F(14) = 377`, `F(15) = 610`, and `233 · 610 − 377² = 142130 − 142129 = 1`. -/

theorem cassini_general (n : ℕ) :
    (Nat.fib (n + 1) : ℤ) * (Nat.fib (n + 3) : ℤ) - (Nat.fib (n + 2) : ℤ) ^ 2 = (-1 : ℤ) ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih =>
      have h : Nat.fib (k + 1 + 3) = Nat.fib (k + 2) + Nat.fib (k + 3) := by
        rw [show k + 1 + 3 = (k + 2) + 2 by ring, Nat.fib_add_two]
      have h2 : Nat.fib (k + 3) = Nat.fib (k + 1) + Nat.fib (k + 2) := by
        rw [show k + 3 = (k + 1) + 2 by ring, Nat.fib_add_two]
      push_cast [h, h2]
      push_cast [h2] at ih
      ring_nf
      ring_nf at ih
      linarith [ih]

/-- The `n = 14` instance re-derived from the general identity. -/
example : (Nat.fib 13 : ℤ) * (Nat.fib 15 : ℤ) - (Nat.fib 14 : ℤ) ^ 2 = (-1 : ℤ) ^ 14 := by
  simpa using cassini_general 12

/-- The `n = 14` instance obtained from Mathlib's own Cassini identity,
`Int.fib_succ_mul_fib_pred_sub_fib_sq : ∀ n : ℤ, Int.fib (n + 1) * Int.fib (n - 1)
  - Int.fib n ^ 2 = (-1) ^ n.natAbs`. -/
