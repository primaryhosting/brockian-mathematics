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

theorem triangle_approx {N d : ℕ} (hd : 1 ≤ d) (hdN : d ≤ N) :
    |((N / d : ℕ) : ℝ) * (((N / d : ℕ) : ℝ) + 1) / 2 / (N : ℝ) ^ 2 - 1 / (2 * (d : ℝ) ^ 2)|
      ≤ 2 / ((N : ℝ) * d) := by
  have hdivmod := Nat.div_add_mod N d
  have hmod : N % d < d := Nat.mod_lt _ (by omega)
  have h1 : (N / d) * d ≤ N := Nat.div_mul_le_self N d
  have h2 : N < (N / d + 1) * d := by
    have h3 : (N / d + 1) * d = d * (N / d) + d := by ring
    omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hm0 : (0 : ℝ) ≤ ((N / d : ℕ) : ℝ) := Nat.cast_nonneg _
  have hA : ((N / d : ℕ) : ℝ) * d ≤ (N : ℝ) := by exact_mod_cast h1
  have hB : (N : ℝ) < (((N / d : ℕ) : ℝ) + 1) * d := by exact_mod_cast h2
  have key : ((N / d : ℕ) : ℝ) * (((N / d : ℕ) : ℝ) + 1) / 2 / (N : ℝ) ^ 2 - 1 / (2 * (d : ℝ) ^ 2)
      = ((d : ℝ) ^ 2 * ((N / d : ℕ) : ℝ) * (((N / d : ℕ) : ℝ) + 1) - (N : ℝ) ^ 2)
        / (2 * (N : ℝ) ^ 2 * (d : ℝ) ^ 2) := by
    field_simp
  have hrhs : 2 / ((N : ℝ) * d) * (2 * (N : ℝ) ^ 2 * (d : ℝ) ^ 2) = 4 * N * d := by
    field_simp; ring
  rw [key, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * (N : ℝ) ^ 2 * (d : ℝ) ^ 2),
    div_le_iff₀ (by positivity), hrhs, abs_le]
  constructor
  · nlinarith [sq_nonneg ((N : ℝ) - ((N / d : ℕ) : ℝ) * d), mul_pos hN0 hd0,
      mul_nonneg hm0 hd0.le]
  · nlinarith [sq_nonneg ((N : ℝ) - ((N / d : ℕ) : ℝ) * d), mul_pos hN0 hd0,
      mul_nonneg hm0 hd0.le]

/-- The truncated Möbius sum `∑_{d ≤ N} μ(d)/d²`. -/
