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

lemma pow_mem_LD {D k : ℕ} {f : (Fin n → Bool) → F} (hf : f ∈ LD F n D) :
    f ^ k ∈ LD F n (k * D) := by
  induction k with
  | zero => simpa using one_mem_LD 0
  | succ k ih =>
      have : f ^ (k + 1) = f ^ k * f := by ring
      rw [this]
      have := mul_mem_LD ih hf
      exact (LD_mono (by ring_nf; omega)) this

