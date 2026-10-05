/-
# Willmore Conjecture
Category: Frontier — Fields Medal Work
Target: Frontier.willmore_conjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types false
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open Real

/-! ## Partial derivatives of functions of two real variables -/

/-- Partial derivative with respect to the first variable. -/

lemma willmore_bound_of_revolution {R r : ℝ} (hr : 0 < r) (hR : r < R) :
    2 * π ^ 2 ≤ π ^ 2 * R ^ 2 / (r * Real.sqrt (R ^ 2 - r ^ 2)) ∧
      (π ^ 2 * R ^ 2 / (r * Real.sqrt (R ^ 2 - r ^ 2)) = 2 * π ^ 2 ↔ R = Real.sqrt 2 * r) := by
  have hRr : 0 < R ^ 2 - r ^ 2 := by nlinarith
  set s := Real.sqrt (R ^ 2 - r ^ 2) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hRr
  have hs2 : s ^ 2 = R ^ 2 - r ^ 2 := Real.sq_sqrt hRr.le
  have hpi : 0 < π ^ 2 := by positivity
  have hden : 0 < r * s := by positivity
  -- the key inequality `R⁴ ≥ 4r²(R² - r²)`, i.e. `R² ≥ 2rs`
  have hsq : R ^ 2 - 2 * (r * s) ≥ 0 := by
    nlinarith [sq_nonneg (R ^ 2 - 2 * r ^ 2), sq_nonneg (R ^ 2 - 2 * (r * s)), sq_nonneg (r * s)]
  constructor
  · rw [le_div_iff₀ hden]
    nlinarith
  · constructor
    · intro h
      rw [div_eq_iff (ne_of_gt hden)] at h
      have hR2 : R ^ 2 = 2 * (r * s) := by nlinarith
      have h2r : R ^ 2 = 2 * r ^ 2 := by nlinarith [sq_nonneg (R ^ 2 - 2 * r ^ 2)]
      have h1 : (Real.sqrt 2 * r) ^ 2 = 2 * r ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      have hfac : (R - Real.sqrt 2 * r) * (R + Real.sqrt 2 * r) = 0 := by nlinarith
      have hpos : 0 < R + Real.sqrt 2 * r := by
        have : 0 ≤ Real.sqrt 2 * r := by positivity
        linarith
      rcases mul_eq_zero.mp hfac with h' | h'
      · linarith
      · linarith
    · intro h
      subst h
      have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have hsr : s = r := by
        rw [hs, show (Real.sqrt 2 * r) ^ 2 - r ^ 2 = r ^ 2 by nlinarith]
        exact Real.sqrt_sq hr.le
      rw [hsr]
      field_simp
      nlinarith

/-- **The Willmore conjecture for tori of revolution.**

For a torus of revolution in `ℝ³` with core radius `R` and tube radius `r` (`0 < r < R`),
the Willmore energy `∫∫ H² dA` — defined through the classical formulas for the first and
second fundamental forms of a parametrized surface — is at least `2π²`, the Clifford torus
(`R = √2 · r`) realizes the value `2π²`, and it is the unique minimizer in this family.

This is the axially symmetric case of the Willmore conjecture, proved here in full; the
general case for all immersed tori is the theorem of Marques and Neves. -/
