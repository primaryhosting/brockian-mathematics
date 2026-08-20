/-
# Robertson Uncertainty
Category: Quantum Computing
Target: QC.robertson_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Robertson Uncertainty
Category: Quantum Computing
Target: QC.robertson_uncertainty
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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types false
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QC

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- An operator `A` on a complex inner product space is *symmetric* (an observable) if
`⟪A x, y⟫ = ⟪x, A y⟫` for all `x, y`. -/

lemma expect_conj (A : H →ₗ[ℂ] H) (hA : IsSymmetricOp A) (ψ : H) :
    (starRingEnd ℂ) (expect A ψ) = expect A ψ := by
  unfold expect
  rw [inner_conj_symm, hA]

/-- For a unit state, `(ΔA)^2 = ⟨A²⟩ - ⟨A⟩²`, i.e. the definition of `stddev`
agrees with the usual variance formula. -/
