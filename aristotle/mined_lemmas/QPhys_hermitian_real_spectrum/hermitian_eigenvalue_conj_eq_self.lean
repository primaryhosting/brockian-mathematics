import Mathlib

/-!
# Hermitian Real Spectrum
Category: Quantum Physics
Target: QPhys.hermitian_real_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped InnerProductSpace

namespace QPhys

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A linear operator on a complex inner product space is *Hermitian* if it is symmetric
with respect to the inner product: `⟪T x, y⟫ = ⟪x, T y⟫` for all `x`, `y`. -/

theorem hermitian_eigenvalue_conj_eq_self (T : E →ₗ[ℂ] E) (hT : IsHermitian T) {μ : ℂ}
    (hμ : HasEigenvalue T μ) : (starRingEnd ℂ) μ = μ := by
  obtain ⟨r, hr⟩ := hermitian_real_spectrum T hT hμ
  simp [hr]

end QPhys

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

