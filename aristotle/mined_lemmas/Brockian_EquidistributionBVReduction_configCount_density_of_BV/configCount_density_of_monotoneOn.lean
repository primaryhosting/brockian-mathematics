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

import Brockian.EquidistributionBVReduction

/-!
# An equidistributed sequence

This file exhibits a concrete sequence in `[0,1)` satisfying
`Brockian.EquidistributionBVReduction.Equidistributed`, showing that the equidistribution
hypothesis of `configCount_density_of_BV` is satisfiable (so the theorem is not vacuous).

The sequence is the "triangular block" sequence: the `k`-th block lists the `k+1` points
`0/(k+1), 1/(k+1), …, k/(k+1)`.
-/

open Filter Set
open scoped Topology

namespace Brockian.EquidistributionBVReduction

/-- Start index of block `k`; block `k` consists of the `k+1` indices
`blockStart k, …, blockStart k + k`. -/

theorem configCount_density_of_monotoneOn (x : ℕ → ℝ) (hx : ∀ n, x n ∈ Set.Ico (0:ℝ) 1)
    (hequi : Equidistributed x) (f : ℝ → ℝ) (hf : MonotoneOn f (Set.Icc 0 1)) :
    Tendsto (fun N => (∑ n ∈ Finset.range N, f (x n)) / N) atTop (𝓝 (∫ t in (0:ℝ)..1, f t)) := by
  set I : ℝ := ∫ t in (0:ℝ)..1, f t with hI
  have hf01 : f 0 ≤ f 1 :=
    hf ⟨le_refl 0, zero_le_one⟩ ⟨zero_le_one, le_refl 1⟩ zero_le_one
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    have hIa : 0 < I - a := sub_pos.2 ha
    obtain ⟨m, hm⟩ := exists_nat_gt ((f 1 - f 0)/(I - a))
    have hm0 : (0:ℝ) < m := lt_of_le_of_lt (div_nonneg (by linarith) hIa.le) hm
    have hmpos : 0 < m := by exact_mod_cast hm0
    have hgap : (f 1 - f 0)/m < I - a := by
      have h := (div_lt_iff₀ hIa).1 hm
      rw [div_lt_iff₀ hm0]
      nlinarith
    have hL : a < ∑ i ∈ Finset.range m, f ((i:ℝ)/m)/m := by
      have h1 := lower_riemann_le_integral f hf hmpos
      have h2 := integral_le_upper_riemann f hf hmpos
      have h3 := upper_sub_lower_riemann f hmpos
      linarith
    have htend := tendsto_step_average x hequi (fun i => f ((i:ℝ)/m)) hmpos
    filter_upwards [(tendsto_order.1 htend).1 a hL] with N hN
    have hlow := lower_sum_le_sum x hx f hf hmpos N
    calc a < (∑ i ∈ Finset.range m,
          f ((i:ℝ)/m) * (configCount x (Set.Ico ((i : ℝ) / m) (((i : ℝ) + 1) / m)) N : ℝ)) / N :=
          hN
      _ ≤ (∑ n ∈ Finset.range N, f (x n)) / N := by gcongr
  · intro b hb
    have hIb : 0 < b - I := sub_pos.2 hb
    obtain ⟨m, hm⟩ := exists_nat_gt ((f 1 - f 0)/(b - I))
    have hm0 : (0:ℝ) < m := lt_of_le_of_lt (div_nonneg (by linarith) hIb.le) hm
    have hmpos : 0 < m := by exact_mod_cast hm0
    have hgap : (f 1 - f 0)/m < b - I := by
      have h := (div_lt_iff₀ hIb).1 hm
      rw [div_lt_iff₀ hm0]
      nlinarith
    have hU : ∑ i ∈ Finset.range m, f (((i:ℝ)+1)/m)/m < b := by
      have h1 := lower_riemann_le_integral f hf hmpos
      have h2 := integral_le_upper_riemann f hf hmpos
      have h3 := upper_sub_lower_riemann f hmpos
      linarith
    have htend := tendsto_step_average x hequi (fun i => f (((i:ℝ)+1)/m)) hmpos
    filter_upwards [(tendsto_order.1 htend).2 b hU] with N hN
    have hup := sum_le_upper_sum x hx f hf hmpos N
    calc (∑ n ∈ Finset.range N, f (x n)) / N
        ≤ (∑ i ∈ Finset.range m,
            f (((i:ℝ)+1)/m) *
              (configCount x (Set.Ico ((i : ℝ) / m) (((i : ℝ) + 1) / m)) N : ℝ)) / N := by gcongr
      _ < b := hN

/-- **Equidistribution ⟹ BV densities.** If a sequence `x` in `[0,1)` is equidistributed
(i.e. the configuration counts of all initial intervals `[0,t)` have density `t`), then for
every function `f` of bounded variation on `[0,1]` the averages `(1/N) ∑_{n < N} f (x n)`
converge to `∫₀¹ f`. This discharges the bounded-variation hypothesis of the reduction. -/
