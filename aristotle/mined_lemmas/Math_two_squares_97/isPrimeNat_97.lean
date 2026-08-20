import Mathlib

/-!
# Two Squares 97 — Mathlib version

Companion to `RequestProject/TwoSquares97.lean`.  Here the statement is phrased
with Mathlib's `Nat.Prime` and derived from the general Mathlib theorem
`Nat.Prime.sq_add_sq` (Fermat's two-squares theorem: a prime `p` with
`p % 4 ≠ 3` is a sum of two squares).
-/

namespace Math

/-- `97` is prime and is a sum of two squares, via `Nat.Prime.sq_add_sq`. -/

theorem isPrimeNat_97 : IsPrimeNat 97 := by
  refine ⟨by decide, ?_⟩
  have h : ∀ m < 98, m ∣ 97 → m = 1 ∨ m = 97 := by decide
  intro m hm
  exact h m (Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) hm)) hm

/-- **Two squares for 97.** The prime `97` is a sum of two squares:
`97 = 4 ^ 2 + 9 ^ 2`. -/
