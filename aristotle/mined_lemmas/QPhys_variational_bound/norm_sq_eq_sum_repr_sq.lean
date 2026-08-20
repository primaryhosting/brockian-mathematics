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

open Module

namespace QPhys

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

omit [FiniteDimensional ℂ V] in
/-- Expansion of the expectation value `⟪ψ, H ψ⟫` in an orthonormal eigenbasis `b` of `H`
with (real) eigenvalues `E`. -/

theorem norm_sq_eq_sum_repr_sq {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ V) (ψ : V) :
    ‖ψ‖ ^ 2 = ∑ i, ‖(b.repr ψ).ofLp i‖ ^ 2 := by
  rw [← b.repr.norm_map ψ, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]

/-- **Key intermediate lemma.**  If `H` is a symmetric (self-adjoint) operator whose
eigenvalues are all bounded below by `E₀`, then the quadratic form of `H` satisfies
`E₀ ‖ψ‖² ≤ ⟪ψ, H ψ⟫` for every state `ψ`. -/
