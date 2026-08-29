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

lemma mon_mem_LD {S : Finset (Fin n)} {D : ℕ} (h : S.card ≤ D) : mon F S ∈ LD F n D := by
  apply Submodule.subset_span
  simp only [monFinset, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_filter]
  exact ⟨S, ⟨Finset.mem_univ _, h⟩, rfl⟩

