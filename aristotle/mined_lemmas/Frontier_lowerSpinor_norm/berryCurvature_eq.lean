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

theorem berryCurvature_eq (th ph : ℝ) :
    berryCurvature th ph = -(1 / 2) * Real.sin th := by
  have hfun : (fun t : ℝ => berryConnPhi t ph) = fun t : ℝ => -(Real.sin (t / 2)) ^ 2 :=
    funext fun t => berryConnPhi_eq t ph
  have hfun2 : (fun s : ℝ => berryConnTheta th s) = fun _ : ℝ => (0 : ℝ) :=
    funext fun s => berryConnTheta_eq th s
  have hd : HasDerivAt (fun t : ℝ => -(Real.sin (t / 2)) ^ 2)
      (-(2 * Real.sin (th / 2) ^ 1 * (Real.cos (th / 2) * (1 / 2)))) th :=
    ((hasDerivAt_sin_half th).pow 2).neg
  have hs : Real.sin th = 2 * Real.sin (th / 2) * Real.cos (th / 2) := by
    have h := Real.sin_two_mul (th / 2)
    rw [show 2 * (th / 2) = th by ring] at h
    exact h
  rw [berryCurvature, hfun, hfun2, hd.deriv, deriv_const, hs]
  ring

/-! ## Chern number and Hall conductance -/

/-- The (first) Chern number of a Berry curvature `F` over the parameter sphere,
`C = (1 / 2π) ∫₀^{2π} ∫₀^{π} F dth dph`. -/
