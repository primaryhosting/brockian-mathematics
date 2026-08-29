import Mathlib

/-!
# Qf Add
Category: Linalg
Target: Zeta23Redux.LinAlg.qf_add
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Zeta23Redux
namespace LinAlg

/-- The quadratic form (sesquilinear form evaluated on the diagonal) associated with a
complex matrix `M`: `qf M x = ⟪x, M x⟫ = star x ⬝ᵥ M *ᵥ x`. -/
noncomputable def qf {n : Type*} [Fintype n] (M : Matrix n n ℂ)
    (x : EuclideanSpace ℂ n) : ℂ :=
  star (x : n → ℂ) ⬝ᵥ M.mulVec (x : n → ℂ)

/-- Additivity of the quadratic form in the matrix argument:
`qf (M + N) x = qf M x + qf N x`. -/
theorem qf_add {n : Type*} [Fintype n] (M N : Matrix n n ℂ)
    (x : EuclideanSpace ℂ n) : qf (M + N) x = qf M x + qf N x := by
  simp [qf, Matrix.add_mulVec, dotProduct_add]

end LinAlg
end Zeta23Redux

