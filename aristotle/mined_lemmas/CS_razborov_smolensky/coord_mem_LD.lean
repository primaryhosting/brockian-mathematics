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

lemma coord_mem_LD (i : Fin n) (D : ℕ) (hD : 1 ≤ D) :
    (fun x => bv F (x i) : (Fin n → Bool) → F) ∈ LD F n D := by
  have : (fun x => bv F (x i) : (Fin n → Bool) → F) = mon F {i} := by
    funext x; simp [mon]
  rw [this]
  exact mon_mem_LD (by simpa using hD)

