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

lemma sum_mem_LD {ι : Type*} (s : Finset ι) (g : ι → (Fin n → Bool) → F) (D : ℕ)
    (h : ∀ i ∈ s, g i ∈ LD F n D) : (∑ i ∈ s, g i) ∈ LD F n D :=
  Submodule.sum_mem _ h

/-- The indicator function of a point of the cube. -/
