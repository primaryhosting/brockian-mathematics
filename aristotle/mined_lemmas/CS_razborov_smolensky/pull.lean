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

def pull {m n : ℕ} (σ : Fin m → Fin n ⊕ Bool) : Circuit m → Circuit n
  | .var i => match σ i with
      | .inl j => .var j
      | .inr b => .const b
  | .const b => .const b
  | .not c => .not (pull σ c)
  | .and k f => .and k (fun i => pull σ (f i))
  | .or k f => .or k (fun i => pull σ (f i))
  | .mod k f => .mod k (fun i => pull σ (f i))

