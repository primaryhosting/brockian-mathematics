import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

lemma ones_append {n p : ℕ} (x : Cube n) (e : Cube p) :
    ones (Fin.append x e) = ones x + ones e := by
  classical
  simp only [ones, Finset.card_filter]
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

