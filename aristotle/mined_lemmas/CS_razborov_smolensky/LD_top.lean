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

lemma LD_top : LD F n n = ⊤ := by
  rw [eq_top_iff]
  intro f _
  have : f = ∑ a : Fin n → Bool, f a • delta F a := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, delta, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single x] <;> simp +contextual [eq_comm]
  rw [this]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (delta_mem_LD a)

/-- The dimension of the space of functions of degree at most `D` is bounded by the
number of monomials of degree at most `D`. -/
