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

lemma harmonic_div_log_tendsto :
    Tendsto (fun N : ℕ => (harmonic N : ℝ) / Real.log N) atTop (𝓝 1) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h0 : Tendsto (fun N : ℕ => 1 / Real.log N) atTop (𝓝 0) := by
    simpa [one_div, Function.comp] using tendsto_inv_atTop_zero.comp hlog
  have hinv : Tendsto (fun N : ℕ => 1 + 1 / Real.log N) atTop (𝓝 1) := by
    simpa using h0.const_add 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hinv ?_ ?_
  · filter_upwards [hlog.eventually_gt_atTop 0, eventually_ge_atTop 1] with N hN hN1
    rw [le_div_iff₀ hN]
    have h1 : Real.log ((N : ℝ) + 1) ≤ (harmonic N : ℝ) := by
      have := log_add_one_le_harmonic N
      push_cast at this
      exact this
    have hNpos : (0:ℝ) < N := by exact_mod_cast hN1
    have h2 : Real.log (N : ℝ) ≤ Real.log ((N : ℝ) + 1) := Real.log_le_log hNpos (by linarith)
    linarith
  · filter_upwards [hlog.eventually_gt_atTop 0] with N hN
    rw [div_le_iff₀ hN]
    have h1 : (harmonic N : ℝ) ≤ 1 + Real.log N := harmonic_le_one_add_log N
    have h3 : (1 + 1 / Real.log N) * Real.log N = Real.log N + 1 := by field_simp
    linarith

/-- The reduction step: given the asymptotics of the harmonic numbers, the total count is
asymptotic to its main term. -/
