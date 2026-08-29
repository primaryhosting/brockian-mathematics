import Mathlib

/-!
# Catalan Mihailescu
Category: Frontier — Prime Numbers
Target: Frontier.Catalan_Mihailescu
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

/-- The full Catalan–Mihăilescu statement: `8` and `9` are the only consecutive
perfect powers, i.e. the only solution of `x ^ p = y ^ q + 1` in integers
`x, y, p, q > 1` is `3 ^ 2 = 2 ^ 3 + 1`. -/

theorem lebesgue {p : ℕ} (hp : 2 ≤ p) (x y : ℕ) (hy : 0 < y) : x ^ p ≠ y ^ 2 + 1 := by
  intro h
  rcases Nat.even_or_odd p with he | ho
  · obtain ⟨k, hk⟩ := he
    have hk1 : 1 ≤ k := by omega
    have hX : (x ^ k) ^ 2 = y ^ 2 + 1 := by rw [← pow_mul, ← h]; congr 1; omega
    set X := x ^ k with hXdef
    have hXy : y < X := by nlinarith [sq_nonneg X]
    nlinarith
  · exact lebesgue_odd ho (by rcases ho with ⟨m, hm⟩; omega) x y hy h

/-! ## The target -/

/-- **Catalan–Mihăilescu, the even-exponent case.**  `3 ^ 2 = 2 ^ 3 + 1` is a solution of
Catalan's equation, and there is no solution `x ^ p = y ^ q + 1` (with `x, y, p, q > 1`)
in which the exponent `q` is even.  (In Mihăilescu's theorem the unique solution has
`q = 3`, so this is a genuine — and unconditional — case of the full statement; the case
of even `q` is Lebesgue's theorem of 1850.) -/
