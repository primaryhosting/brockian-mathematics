/-
/-!
# Hermitian Real Spectrum
Category: Quantum Physics
Target: QPhys.hermitian_real_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

/-!
# Hermitian Real Spectrum
Category: Quantum Physics
Target: QPhys.hermitian_real_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QPhys

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- An operator `A` on a complex inner product space is *Hermitian* if
`⟪A x, y⟫ = ⟪x, A y⟫` for all vectors `x, y`. -/

def IsHermitian (A : E →ₗ[ℂ] E) : Prop :=
  ∀ x y : E, ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ

/-- For a Hermitian operator `A` and an eigenvector `v` with eigenvalue `μ`, the
eigenvalue satisfies `conj μ = μ`. -/
