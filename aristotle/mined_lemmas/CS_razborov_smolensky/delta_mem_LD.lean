import RequestProject.Circuits
import RequestProject.LowDegree

/-!
# MOD_p is not approximable by low degree functions over a field of characteristic q

This is the second half of Smolensky's argument: if the function `x ↦ ζ^{|x|}`
(`ζ` a primitive `p`-th root of unity in a field `F` of characteristic `q`) agrees
with a function of degree `D` on a set `G` of inputs, then `G` is small.
-/

namespace CS

open Finset

open scoped Classical

variable {F : Type*} [Field F] {n : ℕ}

/-- The monomial `∏_{i ∈ S} ζ^{x_i}` in the transformed variables. -/

lemma delta_mem_LD (a : Fin n → Bool) : delta F a ∈ LD F n n := by
  have key : delta F a
      = ∏ i : Fin n, (fun x : Fin n → Bool =>
          if a i then bv F (x i) else 1 - bv F (x i) : (Fin n → Bool) → F) := by
    funext x
    simp only [Finset.prod_apply, delta]
    by_cases hx : x = a
    · subst hx
      rw [if_pos rfl]
      refine (Finset.prod_eq_one fun i _ => ?_).symm
      cases h : x i <;> simp [h]
    · rw [if_neg hx]
      have : ∃ i, x i ≠ a i := by
        by_contra h
        push_neg at h
        exact hx (funext h)
      obtain ⟨i, hi⟩ := this
      refine (Finset.prod_eq_zero (Finset.mem_univ i) ?_).symm
      cases ha : a i <;> cases hxi : x i <;> simp_all
  rw [key]
  have h2 : (∏ i : Fin n, (fun x : Fin n → Bool =>
      if a i then bv F (x i) else 1 - bv F (x i) : (Fin n → Bool) → F))
      ∈ LD F n (∑ _i : Fin n, (1 : ℕ)) := by
    refine prod_mem_LD _ _ _ fun i _ => ?_
    by_cases h : a i
    · simp only [h, if_true]
      exact coord_mem_LD i 1 le_rfl
    · simp only [h, if_false, Bool.false_eq_true]
      exact Submodule.sub_mem _ (one_mem_LD 1) (coord_mem_LD i 1 le_rfl)
  simpa using h2

/-- Every function on the cube has degree at most `n`. -/
