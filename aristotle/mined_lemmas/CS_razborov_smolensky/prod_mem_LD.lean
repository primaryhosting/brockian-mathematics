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

lemma prod_mem_LD {ι : Type*} (s : Finset ι) (g : ι → (Fin n → Bool) → F) (d : ι → ℕ)
    (h : ∀ i ∈ s, g i ∈ LD F n (d i)) : (∏ i ∈ s, g i) ∈ LD F n (∑ i ∈ s, d i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using one_mem_LD 0
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact mul_mem_LD (h a (by simp)) (ih fun i hi => h i (by simp [hi]))

