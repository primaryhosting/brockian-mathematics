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
