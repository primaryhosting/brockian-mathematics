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

theorem total_over_main_tendsto_of_harmonic
    (hHarm : Tendsto (fun N : ℕ => (harmonic N : ℝ) / Real.log N) atTop (𝓝 1)) :
    Tendsto (fun N : ℕ => (totalCount N : ℝ) / mainTerm N) atTop (𝓝 1) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h0 : Tendsto (fun N : ℕ => 1 / Real.log N) atTop (𝓝 0) := by
    simpa [one_div, Function.comp] using tendsto_inv_atTop_zero.comp hlog
  set B : ℕ → ℝ := fun N => ((totalCount N : ℝ) - N * (harmonic N : ℝ)) / ((N : ℝ) * Real.log N)
    with hBdef
  have hBtend : Tendsto B atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ h0
    filter_upwards [hlog.eventually_gt_atTop 0, eventually_ge_atTop 1] with N hN hN1
    have hNpos : (0:ℝ) < N := by exact_mod_cast hN1
    rw [Real.norm_eq_abs, hBdef]
    simp only [abs_div]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have habs : |(N : ℝ) * Real.log N| = (N : ℝ) * Real.log N := abs_of_pos (by positivity)
    rw [habs]
    nlinarith [abs_totalCount_sub_harmonic_le N, hN, hNpos]
  have hsum := hHarm.add hBtend
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [hlog.eventually_gt_atTop 0, eventually_ge_atTop 1] with N hN hN1
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN1
  rw [hBdef, mainTerm]
  field_simp
  ring

/-- **Dirichlet's asymptotic for the divisor summatory function** (leading order):
`(∑_{n ≤ N} d(n)) / (N log N) → 1`. -/
