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

import Mathlib

/-!
# Equidistribution of multiples, and the reduction of the divisor summatory function
to its main term

This file carries out a "level of distribution" style reduction for the simplest possible
sequence, the sequence of all integers, and deduces from it the leading-order asymptotics of
the divisor summatory function.

For a modulus `q`, the number of `n ∈ [1, N]` lying in the residue class `0 mod q` is
`N / q + O(1)` (`abs_countMultiples_sub_le`).  Summing this equidistribution statement over all
moduli `q ≤ N` (a total error of size `O(N)`, `abs_totalCount_sub_harmonic_le`) turns the
"total" count

  `totalCount N = ∑_{n ≤ N} d(n) = ∑_{q ≤ N} #{n ≤ N : q ∣ n}`

into its main term `N * H_N`, where `H_N` is the `N`-th harmonic number.  Since `H_N ∼ log N`,
this gives the Dirichlet asymptotic

  `∑_{n ≤ N} d(n) ∼ N log N`,

which is the statement `total_over_main_tendsto`.
-/

open Filter Finset
open scoped BigOperators Topology

namespace Brockian
namespace EquidistributionBVReduction

/-- The number of integers `n ∈ [1, N]` that are divisible by `q`, i.e. the number of
elements of `[1, N]` in the residue class `0 mod q`. -/

lemma abs_totalCount_sub_harmonic_le (N : ℕ) :
    |(totalCount N : ℝ) - N * (harmonic N : ℝ)| ≤ N := by
  have hcast : ((totalCount N : ℕ) : ℝ) = ∑ q ∈ Finset.Icc 1 N, ((countMultiples N q : ℕ) : ℝ) := by
    rw [totalCount_eq_sum_countMultiples]
    push_cast
    ring
  have hH : ((harmonic N : ℚ) : ℝ) = ∑ q ∈ Finset.Icc 1 N, ((q : ℝ))⁻¹ := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    ring
  rw [hcast, hH, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc |∑ q ∈ Finset.Icc 1 N, ((countMultiples N q : ℝ) - N * (q : ℝ)⁻¹)|
      ≤ ∑ q ∈ Finset.Icc 1 N, |(countMultiples N q : ℝ) - N * (q : ℝ)⁻¹| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _q ∈ Finset.Icc 1 N, 1 := by
        refine Finset.sum_le_sum ?_
        intro q hq
        have hq1 : 1 ≤ q := (Finset.mem_Icc.1 hq).1
        have := abs_countMultiples_sub_le N q hq1
        rwa [div_eq_mul_inv] at this
    _ = N := by simp

/-- The harmonic numbers are asymptotic to the logarithm: `H_N / log N → 1`. -/
