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

import Mathlib

/-!
# Variational Bound
Category: Quantum Physics
Target: QPhys.variational_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped InnerProductSpace

namespace QPhys

variable {ι : Type*} [Fintype ι] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Expansion of `‖ψ‖²` in the coefficients of `ψ` with respect to an orthonormal basis
(Parseval's identity for a finite orthonormal basis). -/

lemma norm_sq_eq_sum_repr_sq (b : OrthonormalBasis ι ℂ V) (ψ : V) :
    ‖ψ‖ ^ 2 = ∑ i, ‖(b.repr ψ).ofLp i‖ ^ 2 := by
  rw [← b.repr.norm_map ψ, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]

/-- If `H` acts diagonally on an orthonormal basis with (real) eigenvalues `Ev`, then the
expectation value `⟨ψ|H|ψ⟩` is the weighted sum `∑ i, Ev i * |cᵢ|²` of the eigenvalues. -/
