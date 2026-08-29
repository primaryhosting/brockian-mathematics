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

lemma orApprox_apply (q : ℕ) {k ℓ : ℕ} (g : Fin k → (Fin n → Bool) → F)
    (s : Fin ℓ → Finset (Fin k)) (x : Fin n → Bool) :
    orApprox q g s x = 1 - ∏ j : Fin ℓ, (1 - (∑ i ∈ s j, g i x) ^ (q - 1)) := by
  simp [orApprox, Finset.prod_apply, Finset.sum_apply]

