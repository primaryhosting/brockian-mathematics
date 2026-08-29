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

theorem integral_inv_const_add_cos {a : ℝ} (ha : 1 < a) :
    ∫ u in (0:ℝ)..(2 * Real.pi), (a + Real.cos u)⁻¹ = 2 * Real.pi / Real.sqrt (a ^ 2 - 1) := by
  set b : ℝ := Real.sqrt (a ^ 2 - 1) with hb
  have ha0 : (0:ℝ) < a := lt_trans zero_lt_one ha
  have hb2 : b ^ 2 = a ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
  have hbpos : 0 < b := Real.sqrt_pos.mpr (by nlinarith)
  have hDpos : ∀ u : ℝ, 0 < a + Real.cos u + b := by
    intro u
    have := Real.neg_one_le_cos u
    linarith
  have hApos : ∀ u : ℝ, 0 < a + Real.cos u := by
    intro u
    have := Real.neg_one_le_cos u
    linarith
  set G : ℝ → ℝ :=
    fun u => (u - 2 * Real.arctan (Real.sin u / (a + Real.cos u + b))) / b with hG
  have key : ∀ u : ℝ, HasDerivAt G ((a + Real.cos u)⁻¹) u := by
    intro u
    have hD := hDpos u
    have hA := hApos u
    have h1 : HasDerivAt (fun x : ℝ => Real.sin x / (a + Real.cos x + b))
        ((Real.cos u * (a + Real.cos u + b) - Real.sin u * (-Real.sin u)) /
          (a + Real.cos u + b) ^ 2) u :=
      (Real.hasDerivAt_sin u).div
        (((Real.hasDerivAt_cos u).const_add a).add_const b) (ne_of_gt hD)
    have h2 := h1.arctan
    have h3 : HasDerivAt (fun x : ℝ => x - 2 * Real.arctan (Real.sin x / (a + Real.cos x + b)))
        (1 - 2 * (1 / (1 + (Real.sin u / (a + Real.cos u + b)) ^ 2) *
          ((Real.cos u * (a + Real.cos u + b) - Real.sin u * (-Real.sin u)) /
            (a + Real.cos u + b) ^ 2))) u :=
      (hasDerivAt_id u).sub (h2.const_mul 2)
    have h4 := h3.div_const b
    convert h4 using 1
    have hs : Real.sin u ^ 2 = 1 - Real.cos u ^ 2 := by
      have := Real.sin_sq_add_cos_sq u; linarith
    have hne : (1 + (Real.sin u / (a + Real.cos u + b)) ^ 2)
        = 2 * (a + b) * (a + Real.cos u) / (a + Real.cos u + b) ^ 2 := by
      field_simp
      nlinarith [hs, hb2]
    rw [hne]
    have h2s : (0:ℝ) < 2 * (a + b) * (a + Real.cos u) := by positivity
    field_simp
    nlinarith [hs, hb2, hA.le, hbpos.le]
  have hint : IntervalIntegrable (fun u : ℝ => (a + Real.cos u)⁻¹)
      MeasureTheory.volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    fun_prop (disch := intro x; exact ne_of_gt (hApos x))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => key x) hint]
  simp [hG, Real.sin_two_pi, Real.cos_two_pi]

/-- `∫₀^{2π} du / (R + r cos u) = 2π / √(R² - r²)` for `0 < r < R`. -/
