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

lemma orApprox_mem {k ℓ q D : ℕ} (g : Fin k → (Fin n → Bool) → F)
    (hg : ∀ i, g i ∈ LD F n D) (s : Fin ℓ → Finset (Fin k)) :
    orApprox q g s ∈ LD F n (ℓ * ((q - 1) * D)) := by
  refine Submodule.sub_mem _ (one_mem_LD _) ?_
  have hfac : ∀ j : Fin ℓ, (1 - (∑ i ∈ s j, g i) ^ (q - 1) : (Fin n → Bool) → F)
      ∈ LD F n ((q - 1) * D) :=
    fun j => Submodule.sub_mem _ (one_mem_LD _)
      (pow_mem_LD (Submodule.sum_mem _ (fun i _ => hg i)))
  have := prod_mem_LD (Finset.univ : Finset (Fin ℓ))
    (fun j => (1 - (∑ i ∈ s j, g i) ^ (q - 1) : (Fin n → Bool) → F))
    (fun _ => (q - 1) * D) (fun j _ => hfac j)
  simpa using this

