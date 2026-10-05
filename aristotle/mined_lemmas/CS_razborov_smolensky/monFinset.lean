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

noncomputable def monFinset (F : Type*) [Field F] (n D : ℕ) : Finset ((Fin n → Bool) → F) :=
  ((Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card ≤ D)).image (mon F)

/-- The space of functions of degree at most `D` on the cube. -/
