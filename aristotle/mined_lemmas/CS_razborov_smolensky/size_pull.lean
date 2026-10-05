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

@[simp] lemma size_pull {m n : ℕ} (σ : Fin m → Fin n ⊕ Bool) (C : Circuit m) :
    (pull σ C).size = C.size := by
  induction C with
  | var i => cases h : σ i <;> simp [pull, size, h]
  | const b => simp [pull, size]
  | not c ih => simp [pull, size, ih]
  | and k f ih => simp [pull, size, ih]
  | or k f ih => simp [pull, size, ih]
  | mod k f ih => simp [pull, size, ih]

