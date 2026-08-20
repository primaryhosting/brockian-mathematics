import Mathlib
/-!
# Willmore Conjecture
Category: Frontier — Fields Medal Work
Target: Frontier.willmore_conjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

The Willmore conjecture (proved by Marques and Neves) states that every immersed torus
`Σ ⊆ ℝ³` satisfies `∫_Σ H² dA ≥ 2π²`, with equality (up to conformal transformations of
`ℝ³`) exactly for the Clifford torus, i.e. the torus of revolution whose radii satisfy
`R = √2 · r`.

This file formalizes and proves the *base case* of the conjecture: the case of tori of
revolution, which is Willmore's original computation and the case that fixes the constant
`2π²`.  Everything is done from first principles:

* for an arbitrary parametrized surface `X : ℝ → ℝ → ℝ³`, the tangent vectors
  `Frontier.surfDu`, `Frontier.surfDv` and the second derivatives are literally `deriv`s
  of `X`; `Frontier.surfMeanCurvature` is the mean curvature computed from the first and
  second fundamental forms, `Frontier.surfAreaElement` is the area element
  `‖X_u × X_v‖`, and `Frontier.willmoreEnergyOf` is the iterated integral `∫∫ H² dA`
  over a fundamental domain `[0, 2π] × [0, 2π]`;
* `Frontier.torusParam` is the usual parametrization of the torus of revolution with
  radii `R > r > 0`, and `Frontier.willmoreEnergy R r` its Willmore energy;
* `Frontier.IsImmersedTorus` and `Frontier.WillmoreConjectureStatement` record the
  statement of the conjecture in full generality.

The main results are

* `Frontier.torusMeanCurvature_eq` and `Frontier.torusAreaElement_eq`: the classical
  formulas `H = (R + 2r cos u) / (2r(R + r cos u))` and `dA = r (R + r cos u)`;
* `Frontier.integral_inv_add_cos` : `∫₀^{2π} du / (R + r cos u) = 2π / √(R² - r²)`;
* `Frontier.willmoreEnergy_eq` : `W(R, r) = π² R² / (r √(R² - r²))`;
* `Frontier.willmore_conjecture` : `2π²` is the least Willmore energy of a torus of
  revolution, and it is attained exactly by the Clifford torus `R = √2 · r`;
* `Frontier.willmore_bound_sharp` : the constant `2π²` in the general conjecture is
  attained by an immersed torus, so it cannot be improved.
-/

open Real Matrix

namespace Frontier

/-! ### Differential geometry of a parametrized surface in `ℝ³`

For a map `X : ℝ → ℝ → ℝ³` we define the tangent vectors, the first and second fundamental
forms, the area element and the mean curvature by the classical formulas.  All derivatives
are honest `deriv`s of `X`. -/

/-- The tangent vector `X_u`. -/

lemma integral_inv_add_cos (R r : ℝ) (hr : 0 < r) (hRr : r < R) :
    (∫ u in (0:ℝ)..(2 * π), (R + r * Real.cos u)⁻¹) = 2 * π / Real.sqrt (R ^ 2 - r ^ 2) := by
  have hR : 0 < R := lt_trans hr hRr
  set k := Real.sqrt (R ^ 2 - r ^ 2) with hkdef
  have hpos : 0 < R ^ 2 - r ^ 2 := by nlinarith
  have hk : 0 < k := Real.sqrt_pos.mpr hpos
  have hk2 : k ^ 2 = R ^ 2 - r ^ 2 := Real.sq_sqrt hpos.le
  set F : ℝ → ℝ := fun u =>
    u / k - (2 / k) * Real.arctan (r * Real.sin u / (R + k + r * Real.cos u)) with hF
  have hderiv : ∀ u : ℝ, HasDerivAt F (R + r * Real.cos u)⁻¹ u := by
    intro u
    have hcos : |Real.cos u| ≤ 1 := Real.abs_cos_le_one u
    have hden : 0 < R + k + r * Real.cos u := by nlinarith [abs_le.mp hcos, hr.le]
    have hden2 : 0 < R + r * Real.cos u := by nlinarith [abs_le.mp hcos]
    have h1 : HasDerivAt (fun u : ℝ => r * Real.sin u / (R + k + r * Real.cos u))
        ((r * Real.cos u * (R + k + r * Real.cos u) - r * Real.sin u * (r * (-Real.sin u)))
          / (R + k + r * Real.cos u) ^ 2) u :=
      ((Real.hasDerivAt_sin u).const_mul r).div
        (((Real.hasDerivAt_cos u).const_mul r).const_add (R + k)) hden.ne'
    have h2 := (Real.hasDerivAt_arctan (r * Real.sin u / (R + k + r * Real.cos u))).comp u h1
    have h3 : HasDerivAt (fun u : ℝ => u / k) (1 / k) u := by
      simpa using (hasDerivAt_id u).div_const k
    have h4 := h3.sub (h2.const_mul (2 / k))
    convert h4 using 1
    have hs : Real.sin u ^ 2 + Real.cos u ^ 2 = 1 := Real.sin_sq_add_cos_sq u
    rw [inv_eq_one_div]
    field_simp
    linear_combination (k * r ^ 2 + R * r ^ 2 + r ^ 3 * Real.cos u) * hs
      + (R + r * Real.cos u + k) * hk2
  have hcont : IntervalIntegrable (fun u => (R + r * Real.cos u)⁻¹) MeasureTheory.volume
      0 (2 * π) := by
    refine Continuous.intervalIntegrable (Continuous.inv₀ (by fun_prop) ?_) _ _
    intro u
    exact (torus_radial_pos hr hRr u).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hderiv u) hcont]
  simp [hF]

/-- The inner integral: for each `v`, `∫₀^{2π} H² dA du = π R² / (2 r √(R² - r²))`. -/
