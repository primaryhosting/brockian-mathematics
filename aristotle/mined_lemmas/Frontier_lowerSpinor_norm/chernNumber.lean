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

def chernNumber (F : ℝ → ℝ → ℝ) : ℝ :=
  (1 / (2 * π)) * ∫ ph in (0:ℝ)..(2 * π), ∫ th in (0:ℝ)..π, F th ph

/-- The TKNN (Kubo-formula) Hall conductance associated with a Berry curvature `F`,
in units set by the electron charge `e` and Planck's constant `hP`:
`σ_xy = (e² / hP) · (1 / 2π) ∫∫ F`. -/
