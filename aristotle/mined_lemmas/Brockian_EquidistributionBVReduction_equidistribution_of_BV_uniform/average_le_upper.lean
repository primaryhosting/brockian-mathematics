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
# Equidistribution Of BV Uniform
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Equidistribution Of BV Uniform
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Brockian.EquidistributionBVReduction

open Filter Finset

/-- `countBelow x N a` is the number of indices `n < N` whose fractional part is `< a`. -/

lemma average_le_upper (x : ℕ → ℝ) (g : ℝ → ℝ) (hg : MonotoneOn g (Set.Icc (0:ℝ) 1))
    (N k : ℕ) (hk : 0 < k) (hN : 0 < N) :
    (∑ n ∈ Finset.range N, g (Int.fract (x n))) / N
      ≤ ∑ j ∈ Finset.range k,
          g (((j:ℝ)+1)/k) * (edf x N (((j:ℝ)+1)/k) - edf x N ((j:ℝ)/k)) := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have key : ∀ j ∈ Finset.range k,
      ∑ n ∈ bin x N k j, g (Int.fract (x n)) ≤ (bin x N k j).card * g (((j:ℝ)+1)/k) := by
    intro j hj
    simp only [Finset.mem_range] at hj
    have hpt : ((j:ℝ)+1)/k ∈ Set.Icc (0:ℝ) 1 := by
      have h := pt_mem k (j+1) hk hj
      rwa [show ((j+1:ℕ):ℝ)/k = ((j:ℝ)+1)/k by push_cast; ring] at h
    have hb : ∀ n ∈ bin x N k j, g (Int.fract (x n)) ≤ g (((j:ℝ)+1)/k) := by
      intro n hn
      simp only [bin, Finset.mem_filter] at hn
      have hfl : Int.fract (x n) < ((j:ℝ)+1)/k := hn.2.2
      exact hg ⟨Int.fract_nonneg _, le_trans hfl.le hpt.2⟩ hpt hfl.le
    calc ∑ n ∈ bin x N k j, g (Int.fract (x n))
        ≤ ∑ _n ∈ bin x N k j, g (((j:ℝ)+1)/k) := Finset.sum_le_sum hb
      _ = (bin x N k j).card * g (((j:ℝ)+1)/k) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hRHS : ∑ j ∈ Finset.range k,
      g (((j:ℝ)+1)/k) * (edf x N (((j:ℝ)+1)/k) - edf x N ((j:ℝ)/k))
      = (∑ j ∈ Finset.range k, ((bin x N k j).card : ℝ) * g (((j:ℝ)+1)/k)) / N := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [edf, edf, ← sub_div, ← card_bin x N k j hk]
    ring
  rw [hRHS, ← sum_bin x g N k hk, div_le_div_iff_of_pos_right hN0]
  exact Finset.sum_le_sum key

/-- The empirical average is at least the lower bin sum. -/
