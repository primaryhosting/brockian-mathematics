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

/-!
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped InnerProductSpace

namespace QPhys

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The expectation value of an observable `A` in the state `ψ`, i.e. the real part of
`⟪ψ, A ψ⟫` (which is automatically real for a symmetric `A` and a unit vector `ψ`). -/

lemma inner_shift_symm {A : H →ₗ[ℂ] H} (hA : ∀ u v : H, ⟪A u, v⟫_ℂ = ⟪u, A v⟫_ℂ)
    (a : ℝ) (ψ v : H) :
    ⟪A ψ - (a : ℂ) • ψ, v⟫_ℂ = ⟪ψ, A v - (a : ℂ) • v⟫_ℂ := by
  rw [inner_sub_left, inner_sub_right, hA, inner_smul_left, inner_smul_right]
  simp [Complex.conj_ofReal]

/-- Version of the uncertainty relation with arbitrary real reference points `a`, `b`
in place of the expectation values. -/
