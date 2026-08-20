import Mathlib

set_option maxHeartbeats 1000000

/-!
# Common machinery for the Kochen–Specker theorem

A *noncontextual hidden-variable assignment* for a quantum system with Hilbert space `E`
assigns to every unit vector (equivalently, to every rank-one projection, i.e. to every
"yes/no question" about the system) a definite truth value, in a way that does not depend on
the context in which the corresponding measurement is performed, and which respects the
quantum-mechanical sum rule: in every complete family of mutually orthogonal rank-one
projections — that is, in every orthonormal basis — exactly one projection is assigned the
value `true`.

We model such an assignment by a function `f : E → Bool`, the sum rule being the hypothesis
`∀ b : Fin n → E, Orthonormal ℝ b → ∃! i, f (b i) = true` (in an `n`-dimensional space an
orthonormal family indexed by `Fin n` is exactly an orthonormal basis).

This file collects the pieces used in dimensions three and four.
-/

namespace Frontier

open scoped RealInnerProductSpace

/-- "Exactly one `true`" in a triple, expressed as a count. -/

theorem kochen_specker_four (f : E4 → Bool)
    (h : ∀ b : Fin 4 → E4, Orthonormal ℝ b → ∃! i, f (b i) = true) : False := by
  have e1 : (f (nrm !₂[0, 0, 0, 1])).toNat + (f (nrm !₂[0, 0, 1, 0])).toNat
      + (f (nrm !₂[1, 1, 0, 0])).toNat + (f (nrm (!₂[1, -1, 0, 0] : E4))).toNat = 1 := by
    apply ks_ctx4 f h <;> norm_num [inner_vec4]
  have e2 : (f (nrm !₂[0, 0, 0, 1])).toNat + (f (nrm !₂[0, 1, 0, 0])).toNat
      + (f (nrm !₂[1, 0, 1, 0])).toNat + (f (nrm (!₂[1, 0, -1, 0] : E4))).toNat = 1 := by
    apply ks_ctx4 f h <;> norm_num [inner_vec4]
  have e3 : (f (nrm !₂[1, -1, 1, -1])).toNat + (f (nrm !₂[1, -1, -1, 1])).toNat
      + (f (nrm !₂[1, 1, 0, 0])).toNat + (f (nrm (!₂[0, 0, 1, 1] : E4))).toNat = 1 := by
    apply ks_ctx4 f h <;> norm_num [inner_vec4]
  have e4 : (f (nrm !₂[1, -1, 1, -1])).toNat + (f (nrm !₂[1, 1, 1, 1])).toNat
      + (f (nrm !₂[1, 0, -1, 0])).toNat + (f (nrm (!₂[0, 1, 0, -1] : E4))).toNat = 1 := by
    apply ks_ctx4 f h <;> norm_num [inner_vec4]
  have e5 : (f (nrm !₂[0, 0, 1, 0])).toNat + (f (nrm !₂[0, 1, 0, 0])).toNat
      + (f (nrm !₂[1, 0, 0, 1])).toNat + (f (nrm (!₂[1, 0, 0, -1] : E4))).toNat = 1 := by
    apply ks_ctx4 f h <;> norm_num [inner_vec4]
  have e6 : (f (nrm !₂[1, -1, -1, 1])).toNat + (f (nrm !₂[1, 1, 1, 1])).toNat
      + (f (nrm !₂[1, 0, 0, -1])).toNat + (f (nrm (!₂[0, 1, -1, 0] : E4))).toNat = 1 := by
    apply ks_ctx4 f h <;> norm_num [inner_vec4]
  have e7 : (f (nrm !₂[1, 1, -1, 1])).toNat + (f (nrm !₂[1, 1, 1, -1])).toNat
      + (f (nrm !₂[1, -1, 0, 0])).toNat + (f (nrm (!₂[0, 0, 1, 1] : E4))).toNat = 1 := by
    apply ks_ctx4 f h <;> norm_num [inner_vec4]
  have e8 : (f (nrm !₂[1, 1, -1, 1])).toNat + (f (nrm !₂[-1, 1, 1, 1])).toNat
      + (f (nrm !₂[1, 0, 1, 0])).toNat + (f (nrm (!₂[0, 1, 0, -1] : E4))).toNat = 1 := by
    apply ks_ctx4 f h <;> norm_num [inner_vec4]
  have e9 : (f (nrm !₂[1, 1, 1, -1])).toNat + (f (nrm !₂[-1, 1, 1, 1])).toNat
      + (f (nrm !₂[1, 0, 0, 1])).toNat + (f (nrm (!₂[0, 1, -1, 0] : E4))).toNat = 1 := by
    apply ks_ctx4 f h <;> norm_num [inner_vec4]
  omega

end Frontier

