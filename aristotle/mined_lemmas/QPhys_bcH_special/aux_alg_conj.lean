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
# Bc H Special
Category: Quantum Physics
Target: QPhys.bcH_special
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bc H Special
Category: Quantum Physics
Target: QPhys.bcH_special
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open NormedSpace

namespace QPhys

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

omit [CompleteSpace 𝔸] in
/-- A function `ℝ → 𝔸` with everywhere vanishing derivative is constant. -/

theorem aux_alg_conj {R : Type*} [Ring R] (X z c e₁ e₂ : R) (h₁ : Commute X e₁)
    (h₂ : Commute X e₂) (hz : X * z = z * X + c) :
    (((-X) * e₁) * z + e₁ * c) * e₂ + (e₁ * z) * (e₂ * X) = 0 := by
  have e1X : (-X) * e₁ * z = -(e₁ * (X * z)) := by
    rw [neg_mul, h₁.eq]; noncomm_ring
  rw [e1X, hz, ← h₂.eq]
  noncomm_ring

/-- **Hadamard's lemma** in the case of a commutator `c = [X, Y]` commuting with `X`:
`e^{tX} Y = (Y + t c) e^{tX}`. -/
