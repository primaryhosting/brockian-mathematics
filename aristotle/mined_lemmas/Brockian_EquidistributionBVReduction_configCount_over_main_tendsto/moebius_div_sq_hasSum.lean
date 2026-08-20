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

/-
# Config Count Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_over_main_tendsto
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
The named hypothesis `configCount_over_main_tendsto` of the equidistribution /
Bombieri–Vinogradov reduction is discharged here: it is Mertens' classical asymptotic
`∑_{q ≤ N} φ(q) ∼ 3 N² / π²`.

The proof follows the standard argument.  Möbius inversion of `∑_{d ∣ n} φ(d) = n`
(`ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq` applied to `Nat.sum_totient`) gives the
hyperbola expansion `∑_{q ≤ N} φ(q) = ∑_{d ≤ N} μ(d) · T(⌊N/d⌋)` with `T(m) = m(m+1)/2`.
Comparing `T(⌊N/d⌋)/N²` with `1/(2d²)` termwise costs `O(1/(Nd))`, so the error is
`O(H_N / N) → 0`, while the truncated Möbius sum converges to
`∑_{d ≥ 1} μ(d)/d² = 1/ζ(2) = 6/π²`; the last identity is taken from Mathlib
(`ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius`, `LSeries_zeta_eq_riemannZeta` and
`riemannZeta_two`).
-/

open ArithmeticFunction Finset Filter

namespace Brockian.EquidistributionBVReduction

/-- The number of *configurations* `(q, a)` with `1 ≤ q ≤ N`, `1 ≤ a ≤ q` and `gcd (a, q) = 1`;
these are the (modulus, primitive residue class) pairs available to an equidistribution /
Bombieri–Vinogradov style reduction with moduli up to `N`.  It equals `∑_{q ≤ N} φ(q)`. -/

theorem moebius_div_sq_hasSum :
    HasSum (fun d : ℕ => (moebius d : ℝ) / (d : ℝ) ^ 2) (6 / Real.pi ^ 2) := by
  have hs : (1 : ℝ) < ((2 : ℂ)).re := by norm_num
  have hz : LSeries (fun n => (zeta n : ℂ)) 2 = riemannZeta 2 := LSeries_zeta_eq_riemannZeta hs
  have hprod := LSeries_zeta_mul_Lseries_moebius hs
  rw [hz, riemannZeta_two] at hprod
  have hmu : LSeries (fun n => (moebius n : ℂ)) 2 = 6 / (Real.pi : ℂ) ^ 2 := by
    have hpi : ((Real.pi : ℂ)) ≠ 0 := by
      simp [Real.pi_ne_zero]
    field_simp at hprod ⊢
    linear_combination hprod
  have hsum : LSeriesHasSum (fun n => (moebius n : ℂ)) 2 (6 / (Real.pi : ℂ) ^ 2) := by
    rw [← hmu]
    exact (LSeriesSummable_moebius_iff.mpr hs).hasSum
  rw [← Complex.hasSum_ofReal]
  have hfun : (fun d : ℕ => (((moebius d : ℝ) / (d : ℝ) ^ 2 : ℝ) : ℂ))
      = LSeries.term (fun n => (moebius n : ℂ)) 2 := by
    funext d
    rcases eq_or_ne d 0 with rfl | hd
    · simp [LSeries.term]
    · rw [LSeries.term_of_ne_zero hd]
      push_cast
      norm_num
  rw [hfun]
  push_cast
  exact hsum

/-- Möbius inversion of `∑_{d ∣ n} φ(d) = n`. -/
