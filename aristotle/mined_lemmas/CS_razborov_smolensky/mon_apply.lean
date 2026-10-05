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

lemma mon_apply (S : Finset (Fin n)) (x : Fin n → Bool) :
    mon F S x = if (∀ i ∈ S, x i = true) then 1 else 0 := by
  unfold mon
  by_cases h : ∀ i ∈ S, x i = true
  · rw [if_pos h]
    exact Finset.prod_eq_one fun i hi => by simp [h i hi]
  · rw [if_neg h]
    push_neg at h
    obtain ⟨i, hi, hix⟩ := h
    exact Finset.prod_eq_zero hi (by simp [bv, Bool.eq_false_iff.mpr hix])

