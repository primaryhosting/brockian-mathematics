/-
# Qf Add
Category: Linalg
Target: Zeta23Redux.LinAlg.qf_add
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Zeta23Redux
namespace LinAlg

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The quadratic form associated with a complex matrix `M`:
`qf M x = ⟪x, M x⟫` for `x` in the Euclidean space `EuclideanSpace ℂ n`. -/
noncomputable def qf (M : Matrix n n ℂ) (x : EuclideanSpace ℂ n) : ℂ :=
  inner ℂ x (Matrix.toEuclideanLin M x)

/-- Quadratic-form additivity: `qf (M + N) x = qf M x + qf N x`. -/
theorem qf_add (M N : Matrix n n ℂ) (x : EuclideanSpace ℂ n) :
    qf (M + N) x = qf M x + qf N x := by
  simp [qf]

end LinAlg
end Zeta23Redux

