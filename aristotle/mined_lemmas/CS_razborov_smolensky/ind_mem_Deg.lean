import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

lemma ind_mem_Deg (a : Cube n) :
    (fun x => if x = a then (1 : F) else 0) ∈ Deg F n n := by
  classical
  have key : (fun x : Cube n => if x = a then (1 : F) else 0)
      = ∏ i ∈ (Finset.univ : Finset (Fin n)),
          (fun x : Cube n => if a i then coord F i x else 1 - coord F i x) := by
    funext x
    simp only [Finset.prod_apply]
    by_cases hx : x = a
    · subst hx
      rw [if_pos rfl]
      exact (Finset.prod_eq_one (fun i _ => by by_cases h : x i <;> simp [coord, h])).symm
    · rw [if_neg hx]
      obtain ⟨i, hi⟩ : ∃ i, x i ≠ a i := by
        by_contra h
        push_neg at h
        exact hx (funext h)
      refine (Finset.prod_eq_zero (Finset.mem_univ i) ?_).symm
      cases hxi : x i <;> cases hai : a i <;> simp [coord, hxi, hai] at hi ⊢
  rw [key]
  have h2 : (∏ i ∈ (Finset.univ : Finset (Fin n)),
      (fun x : Cube n => if a i then coord F i x else 1 - coord F i x))
        ∈ Deg F n (Finset.univ : Finset (Fin n)).card := by
    refine prod_mem_Deg' _ _ (fun i _ => ?_)
    by_cases h : a i
    · simpa [h] using coord_mem_Deg (F := F) i (le_refl 1)
    · simp only [h, if_false, Bool.false_eq_true]
      exact Submodule.sub_mem _ (one_mem_Deg 1) (coord_mem_Deg (F := F) i (le_refl 1))
  simpa using h2

