import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

lemma orPoly_apply {m l : ℕ} (y : Fin m → Cube n → ZMod q) (c : Fin l → Finset (Fin m))
    (x : Cube n) :
    orPoly y c x = if ∀ j, ∑ i ∈ c j, y i x = 0 then 0 else 1 := by
  classical
  unfold orPoly
  by_cases h : ∀ j, ∑ i ∈ c j, y i x = 0
  · rw [if_pos h]
    have : ∀ j : Fin l, (1 - Ez q (∑ i ∈ c j, y i x)) = 1 := by
      intro j; rw [h j, Ez_zero, sub_zero]
    rw [Finset.prod_congr rfl (fun j _ => this j)]
    simp
  · rw [if_neg h]
    push_neg at h
    obtain ⟨j, hj⟩ := h
    rw [Finset.prod_eq_zero (Finset.mem_univ j)]
    · simp
    · rw [Ez_of_ne_zero hj, sub_self]

