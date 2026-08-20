import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

lemma mono_apply (S : Finset (Fin n)) (x : Cube n) :
    mono F S x = if ∀ i ∈ S, x i = true then 1 else 0 := by
  classical
  unfold mono coord
  split
  · next h => exact Finset.prod_eq_one (fun i hi => by simp [h i hi])
  · next h =>
      push_neg at h
      obtain ⟨i, hi, hxi⟩ := h
      refine Finset.prod_eq_zero hi ?_
      have hx : x i = false := by simpa using hxi
      simp [hx]

