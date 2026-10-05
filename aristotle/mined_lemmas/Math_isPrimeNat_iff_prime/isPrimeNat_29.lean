import Mathlib
import RequestProject.TwoSquares29

/-!
Mathlib-facing restatement of `Math.two_squares_29`: the predicate `Math.IsPrimeNat` used in
`RequestProject/TwoSquares29.lean` agrees with Mathlib's `Nat.Prime`, so `29` is a Mathlib-prime
which is a sum of two squares.
-/

namespace Math


theorem isPrimeNat_29 : IsPrimeNat 29 := by
  refine ⟨by decide, fun m hm => ?_⟩
  have hle : m ≤ 29 := Nat.le_of_dvd (by decide) hm
  have key : ∀ k : Nat, k < 30 → k ∣ 29 → k = 1 ∨ k = 29 := by decide
  exact key m (Nat.lt_succ_of_le hle) hm

/-- The prime `29` is a sum of two squares: `29 = 2 ^ 2 + 5 ^ 2`. -/
