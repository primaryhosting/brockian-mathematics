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
open scoped InnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QC

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The expectation value `⟪ψ, T ψ⟫` of an observable `T` in the state `ψ`. -/

lemma norm_inner_sub_inner_le (u v : H) :
    ‖(⟪u, v⟫_ℂ - ⟪v, u⟫_ℂ)‖ ≤ 2 * ‖u‖ * ‖v‖ := by
  have h1 : ‖⟪u, v⟫_ℂ‖ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm u v
  have h2 : ‖⟪v, u⟫_ℂ‖ ≤ ‖u‖ * ‖v‖ := by
    have := norm_inner_le_norm (𝕜 := ℂ) v u
    calc ‖⟪v, u⟫_ℂ‖ ≤ ‖v‖ * ‖u‖ := this
      _ = ‖u‖ * ‖v‖ := by ring
  calc ‖(⟪u, v⟫_ℂ - ⟪v, u⟫_ℂ)‖ ≤ ‖⟪u, v⟫_ℂ‖ + ‖⟪v, u⟫_ℂ‖ := norm_sub_le _ _
    _ ≤ ‖u‖ * ‖v‖ + ‖u‖ * ‖v‖ := add_le_add h1 h2
    _ = 2 * ‖u‖ * ‖v‖ := by ring

/-- The expectation of the commutator equals `⟪u, v⟫ - ⟪v, u⟫` for the centered vectors
`u = (A - ⟪A⟫) ψ` and `v = (B - ⟪B⟫) ψ`. -/
