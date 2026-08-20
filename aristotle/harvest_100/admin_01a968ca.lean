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

set_option grind.warning false

namespace Zeta23Redux.LinAlg

variable {n : Type*} [Fintype n]

/-- The quadratic form associated with a complex matrix `M`, evaluated at a vector `x`
of the Euclidean space `EuclideanSpace ℂ n`: `qf M x = ∑ i, ∑ j, conj (x i) * M i j * x j`. -/
noncomputable def qf (M : Matrix n n ℂ) (x : EuclideanSpace ℂ n) : ℂ :=
  ∑ i, ∑ j, star (x i) * M i j * x j

/-- Additivity of the quadratic form in the matrix argument:
`qf (M + N) x = qf M x + qf N x`. -/
theorem qf_add (M N : Matrix n n ℂ) (x : EuclideanSpace ℂ n) :
    qf (M + N) x = qf M x + qf N x := by
  simp only [qf, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

end Zeta23Redux.LinAlg

