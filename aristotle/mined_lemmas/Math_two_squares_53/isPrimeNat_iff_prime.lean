import Mathlib
import RequestProject.TwoSquares53

/-!
# Two Squares 53 — Mathlib restatement

The target theorem `Math.two_squares_53` lives in `RequestProject/TwoSquares53.lean`,
which is import-free (its statement uses the self-contained predicate `Math.IsPrimeNat`).
Here we record that this predicate agrees with Mathlib's `Nat.Prime`, and restate the
result in Mathlib terms.
-/

namespace Math

/-- `Math.IsPrimeNat` agrees with Mathlib's `Nat.Prime`. -/

theorem isPrimeNat_iff_prime (n : Nat) : IsPrimeNat n ↔ Nat.Prime n := by
  constructor
  · rintro ⟨h2, hd⟩
    refine Nat.prime_def.mpr ⟨h2, fun m hm => ?_⟩
    exact hd m hm
  · intro hp
    exact ⟨hp.two_le, fun m hm => (Nat.Prime.eq_one_or_self_of_dvd hp m hm)⟩

/-- The prime `53` is a sum of two squares, stated with Mathlib's `Nat.Prime`. -/
