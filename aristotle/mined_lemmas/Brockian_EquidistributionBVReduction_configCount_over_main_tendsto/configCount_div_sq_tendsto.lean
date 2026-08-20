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

theorem configCount_div_sq_tendsto :
    Tendsto (fun N : ℕ => configCount N / (N : ℝ) ^ 2) atTop (nhds (3 / Real.pi ^ 2)) := by
  have hzero : Tendsto (fun N : ℕ => configCount N / (N : ℝ) ^ 2 - moebiusPartial N / 2) atTop
      (nhds 0) := by
    refine squeeze_zero_norm (fun N => ?_) (by simpa using harm_div_tendsto.const_mul 2)
    simpa [Real.norm_eq_abs] using configCount_error_bound N
  have h := hzero.add (moebiusPartial_tendsto.div_const 2)
  have hval : (0 : ℝ) + (6 / Real.pi ^ 2) / 2 = 3 / Real.pi ^ 2 := by ring
  rw [hval] at h
  exact h.congr fun N => by ring

/-- **Mertens' theorem** in the form required by the equidistribution / Bombieri–Vinogradov
reduction: the configuration count `∑_{q ≤ N} φ(q)` is asymptotic to its main term `3 N² / π²`. -/
