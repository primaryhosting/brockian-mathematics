import RequestProject.Brockian.Weyl.DeficiencyODE

/-
# Deficiency Represents ODE Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.deficiencyRepresentsODE_of_weakRegularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 does not permit a module docstring before the import line,
so this header is rendered as an ordinary block comment with identical content.)
-/

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

namespace Brockian.Weyl.DeficiencyODE

/-- The formally symmetric first-order Weyl differential expression
`τ u = -i u' + q u` with (continuous, real-valued in the symmetric case) potential `q`.

A function `u` is a *classical* solution of the deficiency equation `τ u = z u`
at the spectral parameter `z` when it is differentiable and satisfies the equation pointwise. -/

theorem weaklySolvesDeficiencyODE_of_solves {q u : ℝ → ℂ} {z : ℂ} (hq : Continuous q)
    (hu : SolvesDeficiencyODE q z u) : WeaklySolvesDeficiencyODE q z u := by
  obtain ⟨hdiff, heq⟩ := hu
  have hderiv : ∀ x : ℝ, deriv u x = Complex.I * (z - q x) * u x := by
    intro x
    have h := heq x
    have h2 : -Complex.I * deriv u x = z * u x - q x * u x := by linear_combination h
    have h3 : Complex.I * (-Complex.I * deriv u x) = deriv u x := by
      linear_combination (-deriv u x) * Complex.I_sq
    calc deriv u x = Complex.I * (-Complex.I * deriv u x) := h3.symm
      _ = Complex.I * (z * u x - q x * u x) := by rw [h2]
      _ = Complex.I * (z - q x) * u x := by ring
  have hcont : Continuous u := hdiff.continuous
  refine ⟨hcont, fun x => ?_⟩
  have hfc : Continuous fun t : ℝ => Complex.I * (z - q t) * u t :=
    continuous_deficiency_integrand hq hcont z
  have hint : ∫ t in (0:ℝ)..x, Complex.I * (z - q t) * u t = u x - u 0 := by
    rw [show (fun t : ℝ => Complex.I * (z - q t) * u t) = deriv u from funext fun t =>
      (hderiv t).symm]
    exact intervalIntegral.integral_deriv_eq_sub (fun t _ => hdiff.differentiableAt)
      ((hfc.congr fun t => (hderiv t).symm).intervalIntegrable 0 x)
  rw [hint]
  ring

/-- Non-vacuity: for the free expression (`q = 0`) the exponential `x ↦ e^{i z x}` is a weak
deficiency element at every spectral parameter `z`. -/
