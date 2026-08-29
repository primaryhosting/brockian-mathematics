import Mathlib
import RequestProject.TwoSquares29

/-!
Mathlib-facing restatement of `Math.two_squares_29`: the predicate `Math.IsPrimeNat` used in
`RequestProject/TwoSquares29.lean` agrees with Mathlib's `Nat.Prime`, so `29` is a Mathlib-prime
which is a sum of two squares.
-/

namespace Math

theorem isPrimeNat_iff_prime {p : ℕ} : IsPrimeNat p ↔ Nat.Prime p := by
  constructor
  · rintro ⟨hp, hdvd⟩
    refine Nat.prime_def.mpr ⟨hp, fun m hm => ?_⟩
    rcases hdvd m hm with h | h
    · exact Or.inl h
    · exact Or.inr h
  · intro hp
    exact ⟨hp.two_le, fun m hm => (Nat.Prime.eq_one_or_self_of_dvd hp m hm)⟩

/-- The prime `29` (in Mathlib's sense) is a sum of two squares. -/

def IsPrimeNat (p : Nat) : Prop := 2 ≤ p ∧ ∀ m : Nat, m ∣ p → m = 1 ∨ m = p

/-- `29` is prime. -/
