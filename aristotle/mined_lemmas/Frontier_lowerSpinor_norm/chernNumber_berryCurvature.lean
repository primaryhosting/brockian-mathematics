import Mathlib

/-!
# Tknn Chern Hall
Category: Frontier Physics
Target: Frontier.tknn_chern_hall
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

noncomputable section

open Complex Real intervalIntegral

/-! ## The two-level Bloch Hamiltonian and its lower band -/

/-- The two-level Bloch Hamiltonian `H(th, ph) = d̂(th,ph) · σ⃗`, where
`d̂ = (sin th cos ph, sin th sin ph, cos th)` is a unit vector and `σ⃗` are the Pauli matrices.
Explicitly `H = [[cos th, sin th e^{-iph}], [sin th e^{iph}, -cos th]]`. -/

theorem chernNumber_berryCurvature : chernNumber berryCurvature = -1 := by
  have hinner : (∫ th in (0:ℝ)..π, (-(1 / 2) * Real.sin th)) = -1 := by
    rw [intervalIntegral.integral_const_mul, integral_sin]
    norm_num
  rw [chernNumber]
  simp_rw [berryCurvature_eq]
  rw [hinner, intervalIntegral.integral_const, smul_eq_mul]
  have hpi : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- **TKNN theorem (base case).**  For the two-level Bloch Hamiltonian
`H(th,ph) = d̂ · σ⃗` with its normalized lower band `lowerSpinor`, the Berry curvature
`F = ∂_th A_ph - ∂_ph A_th` equals `-(1/2) sin th`, its Chern number is the integer `-1`,
and the integer quantum Hall conductance obtained from the TKNN/Kubo integral is exactly
that integer times `e²/h`. -/
