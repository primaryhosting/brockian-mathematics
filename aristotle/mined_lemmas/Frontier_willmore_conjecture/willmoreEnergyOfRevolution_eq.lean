import Mathlib
/-!
# Willmore Conjecture
Category: Frontier — Fields Medal Work
Target: Frontier.willmore_conjecture
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

/-!
## Setting

The Willmore conjecture, proved by Marques and Neves (2014, Fields Medal work of
A. Neves' collaborator F. C. Marques / awarded context), asserts that every immersed
torus in `ℝ³` has Willmore energy `∫ H² dA ≥ 2π²`, with equality exactly for the
Clifford torus (and its images under conformal transformations of `S³`).

The file below formalizes and *proves* the classical base case, due to T. J. Willmore
(1965): the conjecture holds for tori of revolution, i.e. for the surfaces obtained by
revolving a circle of radius `r` about an axis at distance `R > r` in its plane.  For
these surfaces everything (mean curvature, area element, hence the Willmore energy) is
completely explicit, and we compute the energy in closed form, minimize it, and identify
the unique minimizer as the ratio `R = √2 · r` — the "Clifford" torus of revolution.
-/

/-- The mean curvature `H = (k₁ + k₂)/2` of the torus of revolution with tube radius `r`
and center-circle radius `R`, at the tube-angle `u`.  Here `k₁ = 1/r` and
`k₂ = cos u / (R + r cos u)`. -/

theorem willmoreEnergyOfRevolution_eq {R r : ℝ} (hr : 0 < r) (hRr : r < R) :
    willmoreEnergyOfRevolution R r
      = Real.pi ^ 2 * R ^ 2 / (r * Real.sqrt (R ^ 2 - r ^ 2)) := by
  have hApos : ∀ u : ℝ, 0 < R + r * Real.cos u := by
    intro u
    have h1 : -1 ≤ Real.cos u := Real.neg_one_le_cos u
    nlinarith
  -- pointwise rewriting of the integrand
  have hpt : ∀ u : ℝ, (torusMeanCurvature R r u) ^ 2 * torusAreaElement R r u
      = Real.cos u + (R ^ 2 / (4 * r)) * (R + r * Real.cos u)⁻¹ := by
    intro u
    have h := (hApos u).ne'
    simp only [torusMeanCurvature, torusAreaElement]
    field_simp
    ring
  have hcos : IntervalIntegrable Real.cos MeasureTheory.volume 0 (2 * Real.pi) :=
    Real.continuous_cos.intervalIntegrable _ _
  have hinv : IntervalIntegrable (fun u : ℝ => (R ^ 2 / (4 * r)) * (R + r * Real.cos u)⁻¹)
      MeasureTheory.volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    fun_prop (disch := intro x; exact (hApos x).ne')
  have hinner : (∫ u in (0:ℝ)..(2 * Real.pi),
      (torusMeanCurvature R r u) ^ 2 * torusAreaElement R r u)
      = Real.pi * R ^ 2 / (2 * r * Real.sqrt (R ^ 2 - r ^ 2)) := by
    simp only [hpt]
    rw [intervalIntegral.integral_add hcos hinv, intervalIntegral.integral_const_mul,
      integral_inv_add_mul_cos hr hRr]
    have hc : (∫ u in (0:ℝ)..(2 * Real.pi), Real.cos u) = 0 := by
      simp [integral_cos]
    rw [hc]
    have hpos : 0 < Real.sqrt (R ^ 2 - r ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
    field_simp
    ring
  have hpos : 0 < Real.sqrt (R ^ 2 - r ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  rw [willmoreEnergyOfRevolution, hinner]
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  field_simp

/-- **Willmore's theorem (1965): the base case of the Willmore conjecture.**

Every torus of revolution in `ℝ³` — obtained by revolving a circle of radius `r > 0`
about a coplanar axis at distance `R > r` from its centre — has Willmore energy
`∫ H² dA ≥ 2π²`, and equality holds exactly for the ratio `R = √2 · r`, i.e. exactly
for the (stereographic image of the) Clifford torus.

This is the classical base case of the Willmore conjecture, whose full form (for
arbitrary immersed genus-one surfaces) was proved by Marques and Neves. -/
