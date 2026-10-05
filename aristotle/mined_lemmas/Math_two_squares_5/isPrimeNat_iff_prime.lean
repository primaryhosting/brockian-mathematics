import Mathlib
import RequestProject.TwoSquares5

/-!
# Two Squares 5 — link with Mathlib

`RequestProject/TwoSquares5.lean` must begin with a prescribed header comment, so it
cannot contain an `import` line and is stated with a self-contained primality
predicate `Math.IsPrimeNat`.  Here we check that this predicate is exactly
Mathlib's `Nat.Prime`, and restate the main result in Mathlib terms.
-/

namespace Math

/-- The self-contained primality predicate agrees with Mathlib's `Nat.Prime`. -/

theorem isPrimeNat_iff_prime (n : Nat) : IsPrimeNat n ↔ Nat.Prime n := by
  constructor
  · rintro ⟨h2, hdvd⟩
    refine Nat.prime_def.mpr ⟨h2, fun m hm => ?_⟩
    rcases hdvd m hm with h | h
    · exact Or.inl h
    · exact Or.inr h
  · intro hp
    exact ⟨hp.two_le, fun m hm => (Nat.Prime.eq_one_or_self_of_dvd hp m hm)⟩

/-- The prime `5` is a sum of two squares, stated with Mathlib's `Nat.Prime`. -/
