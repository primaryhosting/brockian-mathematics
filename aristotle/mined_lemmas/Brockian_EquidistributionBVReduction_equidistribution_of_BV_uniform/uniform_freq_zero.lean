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
# Reduction of equidistribution to bounded-variation test functions

Let `x : ℕ → ℝ` be a sequence.  Assume that for **every** real function `f` of bounded
variation on `[0,1]` the Birkhoff-type averages

`(1/N) * ∑_{n < N} f (Int.fract (x n))`

converge to `∫₀¹ f`.  We show that the sequence `x` is then equidistributed modulo one, and
moreover *uniformly* so: the counting error over intervals `[a,b) ⊆ [0,1]` tends to `0`
uniformly in the endpoints (i.e. the discrepancy of the sequence tends to `0`).

The main statement is `equidistribution_of_BV_uniform`.  It is unconditional: apart from the
assumption on the sequence itself, no auxiliary result is taken as a hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Set MeasureTheory
open scoped Topology

namespace Brockian

open scoped Classical in
/-- The number of indices `n < N` for which the fractional part of `x n` lies in `[a, b)`. -/

theorem uniform_freq_zero (x : ℕ → ℝ)
    (h : ∀ f : ℝ → ℝ, BoundedVariationOn f (Set.Icc (0:ℝ) 1) →
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f (Int.fract (x n))) / N) atTop
        (𝓝 (∫ t in (0:ℝ)..1, f t)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → |freq x N 0 t - t| < ε := by
  have hε4 : 0 < ε / 4 := by linarith
  obtain ⟨K, hKgt⟩ := exists_nat_gt (4 / ε)
  have hKR : (0:ℝ) < K := lt_of_le_of_lt (by positivity) hKgt
  have hK1 : 1 ≤ K := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (by
    rintro rfl; simp at hKR)
  have hKinv : 1 / (K:ℝ) < ε / 4 := by
    rw [div_lt_iff₀ hKR]
    rw [div_lt_iff₀ hε] at hKgt
    nlinarith
  -- convergence at the grid points
  have hpt : ∀ j : ℕ, ∃ M : ℕ, ∀ N ≥ M,
      |freq x N 0 (min ((j:ℝ)/K) 1) - min ((j:ℝ)/K) 1| < ε / 4 := by
    intro j
    have hb0 : (0:ℝ) ≤ min ((j:ℝ)/K) 1 := le_min (by positivity) zero_le_one
    have hb1 : min ((j:ℝ)/K) 1 ≤ 1 := min_le_right _ _
    have hten := tendsto_freq x h (le_refl (0:ℝ)) hb0 hb1
    rw [Metric.tendsto_atTop] at hten
    obtain ⟨M, hM⟩ := hten (ε / 4) hε4
    exact ⟨M, fun N hN => by simpa [Real.dist_eq, sub_zero] using hM N hN⟩
  choose M hM using hpt
  refine ⟨max 1 ((Finset.range (K + 1)).sup M), le_max_left _ _, ?_⟩
  intro N hN t ht0 ht1
  obtain ⟨j, hjK, hlo, hhi⟩ := grid_bracket K hK1 t ht0 ht1
  have hjle : (j:ℝ) / K ≤ 1 := by
    rw [div_le_one hKR]
    exact_mod_cast Nat.le_of_succ_le hjK
  have hj1le : ((j:ℝ) + 1) / K ≤ 1 := by
    rw [div_le_one hKR]
    exact_mod_cast hjK
  have hgj : min ((j:ℝ)/K) 1 = (j:ℝ)/K := min_eq_left hjle
  have hgj1 : min (((j + 1 : ℕ):ℝ)/K) 1 = ((j:ℝ) + 1)/K := by
    push_cast
    exact min_eq_left hj1le
  have hsupj : M j ≤ N :=
    le_trans (Finset.le_sup (Finset.mem_range.2 (by omega))) (le_trans (le_max_right _ _) hN)
  have hsupj1 : M (j + 1) ≤ N :=
    le_trans (Finset.le_sup (Finset.mem_range.2 (by omega))) (le_trans (le_max_right _ _) hN)
  have hA := hM j N hsupj
  have hB := hM (j + 1) N hsupj1
  rw [hgj] at hA
  rw [hgj1] at hB
  rw [abs_lt] at hA hB ⊢
  have hmono1 : freq x N 0 ((j:ℝ)/K) ≤ freq x N 0 t := freq_mono x N hlo
  have hmono2 : freq x N 0 t ≤ freq x N 0 (((j:ℝ) + 1)/K) := freq_mono x N hhi
  have hstep : ((j:ℝ) + 1)/K = (j:ℝ)/K + 1/K := by ring
  exact ⟨by linarith, by linarith⟩

/-! ### Main theorem -/

/-- **Equidistribution from bounded-variation test functions, uniformly in the interval.**

If for every function `f` of bounded variation on `[0,1]` the averages
`(1/N) ∑_{n<N} f (Int.fract (x n))` converge to `∫₀¹ f`, then the sequence `x` is
equidistributed modulo one, uniformly over all subintervals `[a,b) ⊆ [0,1]`; equivalently,
the discrepancy of `x` tends to `0`. -/
