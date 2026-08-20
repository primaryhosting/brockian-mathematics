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

theorem equidistributed_triSeq : Equidistributed triSeq := by
  intro t ht
  obtain ⟨ht0, ht1⟩ := ht
  have hkey : ∀ᶠ N : ℕ in atTop,
      ‖(configCount triSeq (Set.Ico 0 t) N : ℝ) / N - t‖ ≤ 4 / (blockIdx N : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with N hN1
    set K := blockIdx N with hK
    have hb := blockStart_blockIdx_le N
    have hlt := lt_blockStart_blockIdx_succ N
    rw [blockStart_succ] at hlt
    rw [← hK] at hb hlt
    have hK1 : 1 ≤ K := le_blockIdx (k := 1) (by simpa [blockStart] using hN1)
    have hmono := configCount_mono_bounds triSeq (Set.Ico 0 t) hb
    obtain ⟨hlow, hupp⟩ := configCount_blockStart_bounds t ht0 ht1 K
    have hNb : N - blockStart K ≤ K := by omega
    have hN0 : (0:ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN1
    have hKR : (0:ℝ) < K := by exact_mod_cast hK1
    have hbR : (blockStart K : ℝ) ≤ N := by exact_mod_cast hb
    have hNbR : (N : ℝ) - blockStart K ≤ K := by
      have : ((N - blockStart K : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast hNb
      rwa [Nat.cast_sub hb] at this
    have hC1 : (configCount triSeq (Set.Ico 0 t) (blockStart K) : ℝ)
        ≤ (configCount triSeq (Set.Ico 0 t) N : ℝ) := by exact_mod_cast hmono.1
    have hC2 : (configCount triSeq (Set.Ico 0 t) N : ℝ)
        ≤ (configCount triSeq (Set.Ico 0 t) (blockStart K) : ℝ) + ((N : ℝ) - blockStart K) := by
      have := hmono.2
      have hcast : ((configCount triSeq (Set.Ico 0 t) (blockStart K) + (N - blockStart K) : ℕ) : ℝ)
          = (configCount triSeq (Set.Ico 0 t) (blockStart K) : ℝ) + ((N : ℝ) - blockStart K) := by
        rw [Nat.cast_add, Nat.cast_sub hb]
      calc (configCount triSeq (Set.Ico 0 t) N : ℝ)
          ≤ ((configCount triSeq (Set.Ico 0 t) (blockStart K) + (N - blockStart K) : ℕ) : ℝ) := by
            exact_mod_cast this
        _ = _ := hcast
    -- two-sided estimate
    have habs : |(configCount triSeq (Set.Ico 0 t) N : ℝ) - t * N| ≤ 2 * K := by
      rw [abs_le]
      constructor
      · nlinarith
      · nlinarith
    have hsq : (K:ℝ) * K ≤ 2 * N := by
      have h2 : 2 * blockStart K = K * (K+1) := two_mul_blockStart K
      have : ((K:ℝ)) * ((K:ℝ)+1) = 2 * (blockStart K : ℝ) := by exact_mod_cast h2.symm
      nlinarith
    have heq : (configCount triSeq (Set.Ico 0 t) N : ℝ) / N - t
        = ((configCount triSeq (Set.Ico 0 t) N : ℝ) - t * N) / N := by
      field_simp
    rw [heq, norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hN0]
    rw [div_le_div_iff₀ hN0 hKR]
    nlinarith [abs_nonneg ((configCount triSeq (Set.Ico 0 t) N : ℝ) - t * N)]
  have hzero : Tendsto (fun N : ℕ => 4 / (blockIdx N : ℝ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => (blockIdx N : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp tendsto_blockIdx
    exact h1.const_div_atTop 4
  have := squeeze_zero_norm' hkey hzero
  have h2 := this.add_const t
  simpa using h2

/-- Unconditional instance of the main theorem for the concrete sequence `triSeq`. -/
