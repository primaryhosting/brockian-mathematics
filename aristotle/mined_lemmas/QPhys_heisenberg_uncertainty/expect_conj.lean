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

/-
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QPhys

open ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The expectation value `⟨A⟩ψ = ⟪ψ, A ψ⟫` of an observable `A` in the state `ψ`. -/

lemma expect_conj {A : H →ₗ[ℂ] H} (hA : A.IsSymmetric) (psi : H) :
    conj (expect A psi) = expect A psi := by
  unfold expect
  rw [inner_conj_symm]
  exact hA psi psi

/-- The inner product of two centered observables, in terms of the uncentered ones. -/
