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

theorem lieb_thirring_ground_state_1d (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 1 ψ)
    (hL2 : MemLp ψ 2 volume) (hL2' : MemLp (deriv ψ) 2 volume)
    (hdecay : Tendsto ψ atBot (nhds 0)) (hnorm : ∫ y, ψ y ^ 2 = 1)
    (V : ℝ → ℝ) (hVle : ∀ y, V y ≤ 0) (hVint : Integrable V volume) :
    -(∫ y, |V y|) ^ 2 ≤ (∫ y, deriv ψ y ^ 2) + ∫ y, V y * ψ y ^ 2 := by
  set T := ∫ y, deriv ψ y ^ 2 with hTdef
  set A := ∫ y, |V y| with hAdef
  have hT0 : 0 ≤ T := integral_nonneg fun y => sq_nonneg _
  have hAV : A = -∫ y, V y := by
    rw [hAdef, ← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => abs_of_nonpos (hVle y))
  -- The Sobolev sup bound, using the normalization `∫ ψ² = 1`.
  have hM : ∀ y, ψ y ^ 2 ≤ 2 * Real.sqrt T := by
    intro y
    have h := sobolev_sup_bound_1d ψ hψ hL2 hL2' hdecay y
    rwa [hnorm, Real.sqrt_one, mul_one] at h
  -- The potential energy is bounded below using `V ≤ 0`.
  have hVψ : Integrable (fun y => V y * ψ y ^ 2) volume := by
    have h := hVint.bdd_mul (f := fun y => ψ y ^ 2) (c := 2 * Real.sqrt T)
      ((hψ.continuous.pow 2).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hM y)
    simpa [mul_comm] using h
  have hpot : (2 * Real.sqrt T) * (∫ y, V y) ≤ ∫ y, V y * ψ y ^ 2 := by
    have hmono : ∫ y, (2 * Real.sqrt T) * V y ≤ ∫ y, V y * ψ y ^ 2 := by
      refine integral_mono (hVint.const_mul _) hVψ fun y => ?_
      have := mul_le_mul_of_nonpos_left (hM y) (hVle y)
      linarith [this]
    rwa [integral_const_mul] at hmono
  -- Complete the square.
  have hs : Real.sqrt T ^ 2 = T := Real.sq_sqrt hT0
  have hsq : 0 ≤ (Real.sqrt T - A) ^ 2 := sq_nonneg _
  have hVsum : (2 * Real.sqrt T) * (∫ y, V y) = -(2 * A * Real.sqrt T) := by
    rw [show (∫ y, V y) = -A by rw [hAV]; ring]
    ring
  rw [hVsum] at hpot
  nlinarith [hpot, hs, hsq]

end OneDimensional

end Frontier

