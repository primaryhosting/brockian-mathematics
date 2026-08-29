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
# Equidistribution Of BV Uniform
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Finset MeasureTheory Set
open scoped Topology

namespace Brockian.EquidistributionBVReduction

/-- The frequency with which the fractional parts of the first `N` terms of the sequence `x`
land in the interval `[a, b)`. -/

theorem tendsto_average_of_monotoneOn (hx : UniformlyDistributedMod1 x)
    (hg : MonotoneOn g (Set.Icc (0 : ℝ) 1)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, g (Int.fract (x n))) / N) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, g t)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- choose a fine enough uniform partition
  set M : ℝ := g 1 - g 0 with hM
  have hM0 : 0 ≤ M := by
    have := hg (by norm_num : (0:ℝ) ∈ Set.Icc (0:ℝ) 1) (by norm_num : (1:ℝ) ∈ Set.Icc (0:ℝ) 1)
      (by norm_num)
    simp only [hM]; linarith
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * M / ε)
  set k : ℕ := m + 1 with hkdef
  have hk : 0 < k := Nat.succ_pos m
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hkm : 2 * M / ε < k := by
    refine hm.trans ?_
    rw [hkdef]; push_cast; linarith
  have hMk : M / k < ε / 2 := by
    rw [div_lt_iff₀ hk0]
    rw [div_lt_iff₀ hε] at hkm
    linarith
  -- lower and upper Riemann sums
  set U : ℝ := ∑ j ∈ Finset.range k, g ((j : ℝ) / k) / k with hU
  set V : ℝ := ∑ j ∈ Finset.range k, g (((j : ℝ) + 1) / k) / k with hV
  have hVU : V - U = M / k := by
    rw [hU, hV, ← Finset.sum_sub_distrib]
    have : ∀ j ∈ Finset.range k,
        g (((j : ℝ) + 1) / k) / k - g ((j : ℝ) / k) / k
          = ((fun i : ℕ => g ((i : ℝ) / k) / k) (j + 1))
            - ((fun i : ℕ => g ((i : ℝ) / k) / k) j) := by
      intro j _; dsimp only; push_cast; ring
    rw [Finset.sum_congr rfl this, Finset.sum_range_sub (fun i : ℕ => g ((i : ℝ) / k) / k) k]
    rw [Nat.cast_zero, zero_div]
    have h1 : (k : ℝ) / k = 1 := by field_simp
    rw [h1, hM]
    ring
  have hUI : U ≤ ∫ t in (0:ℝ)..1, g t := lower_sum_le_integral hg hk
  have hIV : (∫ t in (0:ℝ)..1, g t) ≤ V := integral_le_upper_sum hg hk
  -- the counting sums converge
  have hlow := tendsto_step_sum hx hk (fun j => g ((j : ℝ) / k))
  have hupp := tendsto_step_sum hx hk (fun j => g (((j : ℝ) + 1) / k))
  rw [Metric.tendsto_atTop] at hlow hupp
  obtain ⟨N₁, hN₁⟩ := hlow (ε / 4) (by linarith)
  obtain ⟨N₂, hN₂⟩ := hupp (ε / 4) (by linarith)
  refine ⟨max (max N₁ N₂) 1, fun N hN => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right _ _) hN)
  have hNR : (0:ℝ) < N := by exact_mod_cast hNpos
  have hlowN := hN₁ N hN1
  have huppN := hN₂ N hN2
  rw [Real.dist_eq, abs_lt] at hlowN huppN
  -- the sandwich
  have hcast : ∀ c : ℕ → ℝ,
      ∑ j ∈ Finset.range k, c j *
        ((((Finset.range N).filter
          (fun n => Int.fract (x n) ∈ Set.Ico ((j : ℝ) / k) (((j : ℝ) + 1) / k))).card : ℝ) / N)
        = (∑ j ∈ Finset.range k, c j *
        (((Finset.range N).filter
          (fun n => Int.fract (x n) ∈ Set.Ico ((j : ℝ) / k) (((j : ℝ) + 1) / k))).card : ℝ)) / N
      := by
    intro c
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hlowSand : ∑ j ∈ Finset.range k, g ((j : ℝ) / k) *
        ((((Finset.range N).filter
          (fun n => Int.fract (x n) ∈ Set.Ico ((j : ℝ) / k) (((j : ℝ) + 1) / k))).card : ℝ) / N)
      ≤ (∑ n ∈ Finset.range N, g (Int.fract (x n))) / N := by
    rw [hcast (fun j => g ((j : ℝ) / k))]
    gcongr
    exact lower_step_le_sum hg x hk N
  have huppSand : (∑ n ∈ Finset.range N, g (Int.fract (x n))) / N
      ≤ ∑ j ∈ Finset.range k, g (((j : ℝ) + 1) / k) *
        ((((Finset.range N).filter
          (fun n => Int.fract (x n) ∈ Set.Ico ((j : ℝ) / k) (((j : ℝ) + 1) / k))).card : ℝ) / N)
      := by
    rw [hcast (fun j => g (((j : ℝ) + 1) / k))]
    gcongr
    exact sum_le_upper_step hg x hk N
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor <;> linarith

end Monotone

/-- **Equidistribution theorem for functions of bounded variation.**

If `x : ℕ → ℝ` is uniformly distributed mod 1 and `f` has bounded variation on `[0, 1]`, then the
averages `(1/N) ∑_{n < N} f (frac (x n))` converge to `∫₀¹ f`.  -/
