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

lemma yMon_apply (ζ : F) (S : Finset (Fin n)) (x : Fin n → Bool) :
    yMon ζ S x = ζ ^ ((S.filter (fun i => x i = true)).card) := by
  unfold yMon
  rw [← Finset.prod_filter_mul_prod_filter_not S (fun i => x i = true)]
  have h1 : ∀ i ∈ S.filter (fun i => x i = true), (1 + (ζ - 1) * bv F (x i)) = ζ := by
    intro i hi
    simp only [Finset.mem_filter] at hi
    simp [hi.2, bv]
  have h2 : ∀ i ∈ S.filter (fun i => ¬ (x i = true)), (1 + (ζ - 1) * bv F (x i)) = 1 := by
    intro i hi
    simp only [Finset.mem_filter] at hi
    simp [Bool.eq_false_iff.mpr hi.2, bv]
  rw [Finset.prod_congr rfl h1, Finset.prod_congr rfl h2]
  simp

