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

lemma sum_le_upper_sum (x : ℕ → ℝ) (hx : ∀ n, x n ∈ Set.Ico (0:ℝ) 1) (f : ℝ → ℝ)
    (hf : MonotoneOn f (Set.Icc 0 1)) {m : ℕ} (hm : 0 < m) (N : ℕ) :
    ∑ n ∈ Finset.range N, f (x n)
      ≤ ∑ i ∈ Finset.range m,
          f (((i : ℝ) + 1) / m) *
            (configCount x (Set.Ico ((i : ℝ) / m) (((i : ℝ) + 1) / m)) N : ℝ) := by
  classical
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  rw [sum_fiberwise_aux x hx (fun n => f (x n)) hm N]
  refine Finset.sum_le_sum ?_
  intro i hi
  have hi' : i < m := Finset.mem_range.1 hi
  have hmem : (((i:ℝ)+1)/m) ∈ Set.Icc (0:ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hm']
    exact_mod_cast hi'
  rw [configCount_eq_fiber_card x hx hm N i]
  have hle : ∀ n ∈ (Finset.range N).filter (fun n => ⌊(m:ℝ) * x n⌋₊ = i),
      f (x n) ≤ f (((i:ℝ)+1)/m) := by
    intro n hn
    have hfl : ⌊(m:ℝ) * x n⌋₊ = i := (Finset.mem_filter.1 hn).2
    have hlt : (m:ℝ) * x n < (i:ℝ) + 1 := by
      have h := Nat.lt_floor_add_one ((m:ℝ) * x n)
      rw [hfl] at h
      exact_mod_cast h
    refine hf ⟨(hx n).1, (hx n).2.le⟩ hmem ?_
    rw [le_div_iff₀ hm']
    nlinarith
  have hcard := Finset.sum_le_card_nsmul
    ((Finset.range N).filter (fun n => ⌊(m:ℝ) * x n⌋₊ = i)) (fun n => f (x n))
    (f (((i:ℝ)+1)/m)) hle
  simpa [nsmul_eq_mul, mul_comm] using hcard

/-- Averages of step sums converge to the corresponding Riemann sum. -/
