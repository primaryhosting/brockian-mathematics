import Mathlib
import RequestProject.TwoSquares113

/-!
# Two Squares 113 (Mathlib restatement)

Restatement of `Math.two_squares_113` using Mathlib's `Nat.Prime`.
-/

namespace Math

/-- `Math.IsPrimeNat` agrees with Mathlib's `Nat.Prime`. -/

theorem isPrimeNat_iff_prime (p : Nat) : IsPrimeNat p ↔ Nat.Prime p := by
  constructor
  · rintro ⟨hp, hd⟩
    exact Nat.prime_def.mpr ⟨hp, fun d hdvd => hd d hdvd⟩
  · intro hp
    exact ⟨hp.two_le, fun d hdvd => (Nat.Prime.eq_one_or_self_of_dvd hp d hdvd)⟩

/-- The prime `113` is a sum of two squares, stated with Mathlib's `Nat.Prime`. -/
