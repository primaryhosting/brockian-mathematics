import Mathlib

/-!
# Qf Add
Category: Linalg
Target: Zeta23Redux.LinAlg.qf_add
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators
open scoped Classical
open scoped Matrix

set_option maxHeartbeats 800000
set_option autoImplicit false

namespace Zeta23Redux
namespace LinAlg

variable {n : Type*} [Fintype n]

/-- The (Hermitian) quadratic form attached to a complex matrix `M`:
`qf M x = xᴴ M x = ∑ i, ∑ j, conj (x i) * M i j * x j`. -/
noncomputable def qf (M : Matrix n n ℂ) (x : EuclideanSpace ℂ n) : ℂ :=
  dotProduct (star (x : n → ℂ)) (M.mulVec (x : n → ℂ))

/-- Quadratic-form additivity: `qf (M + N) x = qf M x + qf N x`. -/
theorem qf_add (M N : Matrix n n ℂ) (x : EuclideanSpace ℂ n) :
    qf (M + N) x = qf M x + qf N x := by
  simp [qf, Matrix.add_mulVec, dotProduct_add]

end LinAlg
end Zeta23Redux

import Mathlib

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

