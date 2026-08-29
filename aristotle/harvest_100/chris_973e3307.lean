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
def SolvesDeficiencyODE (q : ℝ → ℂ) (z : ℂ) (u : ℝ → ℂ) : Prop :=
  Differentiable ℝ u ∧ ∀ x : ℝ, -Complex.I * deriv u x + q x * u x = z * u x

/-- A *weak* deficiency element at the spectral parameter `z`: `u` is merely continuous and
satisfies the integrated (Volterra) form of `τ u = z u`, i.e.
`u x = u 0 + ∫ t in 0..x, i (z - q t) u t`.

This is the form in which deficiency elements of the minimal operator are produced: a priori one
only knows that `u` is (locally integrable and) a distributional solution, with the integrated
identity coming from the definition of the adjoint, and *not* that `u` is differentiable. -/
def WeaklySolvesDeficiencyODE (q : ℝ → ℂ) (z : ℂ) (u : ℝ → ℂ) : Prop :=
  Continuous u ∧ ∀ x : ℝ, u x = u 0 + ∫ t in (0:ℝ)..x, Complex.I * (z - q t) * u t

/-- The integrand of the Volterra form is continuous. -/
theorem continuous_deficiency_integrand {q u : ℝ → ℂ} (hq : Continuous q) (hu : Continuous u)
    (z : ℂ) : Continuous fun t : ℝ => Complex.I * (z - q t) * u t := by
  fun_prop

/-- **Weak regularity is automatic.**  A weak (Volterra) deficiency element of the Weyl expression
`τ u = -i u' + q u` with continuous potential `q` is automatically differentiable, with derivative
given by the ODE right-hand side. -/
theorem hasDerivAt_of_weaklySolves {q u : ℝ → ℂ} {z : ℂ} (hq : Continuous q)
    (hu : WeaklySolvesDeficiencyODE q z u) (x : ℝ) :
    HasDerivAt u (Complex.I * (z - q x) * u x) x := by
  obtain ⟨hcont, heq⟩ := hu
  have hf : Continuous fun t : ℝ => Complex.I * (z - q t) * u t :=
    continuous_deficiency_integrand hq hcont z
  have h1 : HasDerivAt
      (fun y : ℝ => u 0 + ∫ t in (0:ℝ)..y, Complex.I * (z - q t) * u t)
      (Complex.I * (z - q x) * u x) x := by
    have h0 := intervalIntegral.integral_hasDerivAt_right
      (hf.intervalIntegrable 0 x)
      (hf.stronglyMeasurable.stronglyMeasurableAtFilter) hf.continuousAt
    simpa using h0.const_add (u 0)
  have hfun : (fun y : ℝ => u 0 + ∫ t in (0:ℝ)..y, Complex.I * (z - q t) * u t) = u :=
    funext fun y => (heq y).symm
  rwa [hfun] at h1

/-- **Deficiency elements represent solutions of the ODE, without a regularity assumption.**

If `q` is a continuous potential and `u` is a weak (Volterra-form) deficiency element of the
formally symmetric Weyl expression `τ u = -i u' + q u` at the spectral parameter `z`, then `u` is
in fact a classical solution of the ordinary differential equation `τ u = z u`.

The `weak regularity` hypothesis (differentiability of `u`) that normally accompanies this
statement in the literature is *discharged*: it follows from the integrated equation together with
continuity of the integrand, via the fundamental theorem of calculus
(`intervalIntegral.integral_hasDerivAt_right`). -/
theorem deficiencyRepresentsODE_of_weakRegularity {q u : ℝ → ℂ} {z : ℂ} (hq : Continuous q)
    (hu : WeaklySolvesDeficiencyODE q z u) : SolvesDeficiencyODE q z u := by
  refine ⟨fun x => (hasDerivAt_of_weaklySolves hq hu x).differentiableAt, fun x => ?_⟩
  rw [(hasDerivAt_of_weaklySolves hq hu x).deriv]
  linear_combination (-(z - q x) * u x) * Complex.I_sq

/-- Conversely, every classical solution of the deficiency equation satisfies the integrated
(Volterra) form, so the two notions coincide for continuous potentials. -/
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
theorem weaklySolves_exp (z : ℂ) :
    WeaklySolvesDeficiencyODE (fun _ => 0) z (fun x : ℝ => Complex.exp (Complex.I * z * x)) := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x : ℝ => Complex.exp (Complex.I * z * x))
      (Complex.exp (Complex.I * z * x) * (Complex.I * z)) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => Complex.I * z * (x : ℂ)) (Complex.I * z) x := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (Complex.I * z)
    exact h1.cexp
  refine weaklySolvesDeficiencyODE_of_solves continuous_const
    ⟨fun x => (hd x).differentiableAt, fun x => ?_⟩
  rw [(hd x).deriv]
  simp only [zero_mul]
  linear_combination (-z * Complex.exp (Complex.I * z * x)) * Complex.I_sq

end Brockian.Weyl.DeficiencyODE

