/-
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace
open Matrix

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

set_option grind.warning false

namespace QPhys

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The spread (standard deviation) of the observable `A` in the state `psi`:
the norm of `A psi` after subtracting its mean value `⟪psi, A psi⟫ • psi`. -/

lemma conj_expectation {A : H →ₗ[ℂ] H} (hA : IsSymmetricOp A) (psi : H) :
    (starRingEnd ℂ) (⟪psi, A psi⟫_ℂ) = ⟪psi, A psi⟫_ℂ := by
  rw [inner_conj_symm, hA]

/-- For a symmetric operator `A` and a normalized state, the square of the spread is the
usual variance `⟨A²⟩ - ⟨A⟩²`. -/
