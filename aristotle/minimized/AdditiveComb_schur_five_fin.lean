/-
# Schur Five
Category: Frontier Wave 2 (deeper machinery)
Target: AdditiveComb.schur_five
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Schur Five
Category: Frontier Wave 2 (deeper machinery)
Target: AdditiveComb.schur_five
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace AdditiveComb

/-- The Schur instance on `{1,2,3,4,5}` phrased for colourings indexed by `Fin 5`,
where the index `i` stands for the integer `i + 1`.  Proved by exhaustive check over
the `2^5 = 32` colourings. -/

theorem schur_five_fin (g : Fin 5 → Bool) :
    ∃ x y z : Fin 5,
      ((x : ℕ) + 1) + ((y : ℕ) + 1) = (z : ℕ) + 1 ∧ g x = g y ∧ g y = g z := by
  revert g
  decide

/-- **Schur's theorem, the instance `S(2) < 5`.**
For every `2`-colouring `f` of `{1,2,3,4,5}` there is a monochromatic Schur triple:
elements `x, y, z ∈ {1,…,5}` with `x + y = z` and `f x = f y = f z`. -/
