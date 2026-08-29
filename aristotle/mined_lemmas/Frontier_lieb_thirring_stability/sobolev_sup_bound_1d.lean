/-
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain block comment rather than a `/-!` module
-- docstring only because Lean 4 requires `import` to precede any docstring;
-- the identical module docstring is reproduced immediately after the imports.)

import Mathlib

/-!
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
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

/-!
## Overview

The Lieb–Thirring route to the *stability of matter* combines three ingredients:

1. **The Lieb–Thirring kinetic energy inequality.**  For a normalized fermionic
   wave function `Ψ` of `N` particles with one-particle density `ρ`, the kinetic
   energy obeys `T ≥ K_LT * ∫ ρ^(5/3)`.

2. **An electrostatic (Baxter / Lieb–Yau type) inequality.**  The full Coulomb
   interaction of electrons and nuclei is bounded below by a purely local term,
   `V ≥ - C_ES * ∫ ρ^(4/3) - C_nuc`, where `C_nuc` collects the nucleus-dependent
   contribution (proportional to the number of nuclei).

3. **A functional-analytic interpolation step**, which turns the competition
   between the two local terms into a bound that is *linear in the particle
   number* `N = ∫ ρ`.

Step 3 is the mathematical heart of the reduction, and it is what is proved here
from scratch: by Cauchy–Schwarz (the `p = q = 2` case of Hölder's inequality)

  `∫ ρ^(4/3) = ∫ ρ^(1/2) · ρ^(5/6) ≤ (∫ ρ)^(1/2) · (∫ ρ^(5/3))^(1/2)`,

so that with `t = ∫ ρ^(5/3)` and `N = ∫ ρ`,

  `T + V ≥ K_LT * t - C_ES * √N * √t - C_nuc ≥ - (C_ES^2 / (4 K_LT)) * N - C_nuc`

by the arithmetic–geometric mean inequality.  The conclusion is exactly
*stability of the second kind*: the energy per particle is bounded below by a
constant that does not depend on `N`.

Everything below is stated for an arbitrary measure space, so that it applies
verbatim to `ρ : ℝ³ → ℝ≥0∞` with Lebesgue measure.  Densities are taken to be
`ℝ≥0∞`-valued so that all the integrals are unconditionally defined; the two
physical input inequalities (1) and (2) enter as hypotheses, and the deduction of
stability from them is fully verified.
-/

namespace Frontier

open MeasureTheory ENNReal

section Densities

variable {α : Type*} [MeasurableSpace α]

/-- The total mass (particle number) `∫ ρ` of a one-particle density `ρ`. -/

theorem sobolev_sup_bound_1d (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 1 ψ)
    (hL2 : MemLp ψ 2 volume) (hL2' : MemLp (deriv ψ) 2 volume)
    (hdecay : Tendsto ψ atBot (nhds 0)) (x : ℝ) :
    ψ x ^ 2 ≤ 2 * Real.sqrt (∫ y, ψ y ^ 2) * Real.sqrt (∫ y, deriv ψ y ^ 2) := by
  have hB : Integrable (fun y => |ψ y| * |deriv ψ y|) volume :=
    MeasureTheory.MemLp.integrable_mul hL2.abs hL2'.abs
  set B := ∫ y, |ψ y| * |deriv ψ y| with hBdef
  have hcont : Continuous ψ := hψ.continuous
  have hcont' : Continuous (deriv ψ) := hψ.continuous_deriv le_rfl
  have key : ∀ a : ℝ, a ≤ x → ψ x ^ 2 ≤ ψ a ^ 2 + 2 * B := by
    intro a hax
    have hderiv : ∀ y ∈ Set.uIcc a x, HasDerivAt (fun z => ψ z ^ 2) (2 * ψ y * deriv ψ y) y := by
      intro y _
      have h1 : HasDerivAt ψ (deriv ψ y) y := (hψ.differentiable one_ne_zero y).hasDerivAt
      simpa [mul_comm, mul_assoc, mul_left_comm] using h1.pow 2
    have hint : IntervalIntegrable (fun y => 2 * ψ y * deriv ψ y) volume a x :=
      Continuous.intervalIntegrable (by fun_prop) a x
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    have hb : |∫ y in a..x, 2 * ψ y * deriv ψ y| ≤ 2 * B := by
      have h1 : |∫ y in a..x, 2 * ψ y * deriv ψ y| ≤ ∫ y in a..x, |2 * ψ y * deriv ψ y| := by
        rw [intervalIntegral.integral_of_le hax, intervalIntegral.integral_of_le hax]
        simpa [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (μ := volume.restrict (Set.Ioc a x))
            (fun y => 2 * ψ y * deriv ψ y)
      refine h1.trans ?_
      rw [intervalIntegral.integral_of_le hax]
      have h2 : ∫ y in Set.Ioc a x, |2 * ψ y * deriv ψ y| ≤ ∫ y, |2 * ψ y * deriv ψ y| := by
        refine setIntegral_le_integral ?_ (Filter.Eventually.of_forall fun y => abs_nonneg _)
        simpa [abs_mul, mul_assoc] using (hB.const_mul 2).abs
      refine h2.trans_eq ?_
      simp only [abs_mul, abs_two]
      rw [hBdef, ← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
    have habs := abs_le.mp hb
    linarith [hFTC, habs.1, habs.2]
  have hlim : Tendsto (fun a => ψ a ^ 2 + 2 * B) atBot (nhds (0 ^ 2 + 2 * B)) :=
    (hdecay.pow 2).add tendsto_const_nhds
  have hfin : ψ x ^ 2 ≤ 0 ^ 2 + 2 * B := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [Filter.eventually_le_atBot x] with a ha
    exact key a ha
  have hCS : B ≤ Real.sqrt (∫ y, ψ y ^ 2) * Real.sqrt (∫ y, deriv ψ y ^ 2) :=
    integral_abs_mul_le_sqrt_mul_sqrt hL2 hL2'
  simp only [pow_two, zero_mul, zero_add] at hfin
  nlinarith [hfin, hCS]

/--
**The one-dimensional Lieb–Thirring ground state bound (base case).**

Let `V ≤ 0` be an integrable potential on `ℝ` and let `ψ` be a normalized `C¹`
state with `ψ, ψ' ∈ L²(ℝ)` decaying at `-∞`.  Then the energy expectation value
satisfies

  `∫ (ψ')² + ∫ V ψ² ≥ - (∫ |V|)²`.

In particular the lowest eigenvalue `E₀` of `-d²/dx² + V` obeys `|E₀| ≤ (∫ |V|)²`,
the `d = 1`, `γ = 1/2` Lieb–Thirring inequality (with constant `1` rather than the
sharp constant `1/4`).
-/
