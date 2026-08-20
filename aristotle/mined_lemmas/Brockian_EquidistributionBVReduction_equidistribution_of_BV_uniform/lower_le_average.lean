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

lemma lower_le_average (x : ℕ → ℝ) (g : ℝ → ℝ) (hg : MonotoneOn g (Set.Icc (0:ℝ) 1))
    (N k : ℕ) (hk : 0 < k) (hN : 0 < N) :
    ∑ j ∈ Finset.range k,
        g ((j:ℝ)/k) * (edf x N (((j:ℝ)+1)/k) - edf x N ((j:ℝ)/k))
      ≤ (∑ n ∈ Finset.range N, g (Int.fract (x n))) / N := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have key : ∀ j ∈ Finset.range k,
      ((bin x N k j).card : ℝ) * g ((j:ℝ)/k) ≤ ∑ n ∈ bin x N k j, g (Int.fract (x n)) := by
    intro j hj
    simp only [Finset.mem_range] at hj
    have hpt : ((j:ℝ)/k) ∈ Set.Icc (0:ℝ) 1 := pt_mem k j hk (by omega)
    have hpt' : ((j:ℝ)+1)/k ∈ Set.Icc (0:ℝ) 1 := by
      have h := pt_mem k (j+1) hk hj
      rwa [show ((j+1:ℕ):ℝ)/k = ((j:ℝ)+1)/k by push_cast; ring] at h
    have hb : ∀ n ∈ bin x N k j, g ((j:ℝ)/k) ≤ g (Int.fract (x n)) := by
      intro n hn
      simp only [bin, Finset.mem_filter] at hn
      exact hg hpt ⟨Int.fract_nonneg _, le_trans hn.2.2.le hpt'.2⟩ hn.2.1
    calc ((bin x N k j).card : ℝ) * g ((j:ℝ)/k)
        = ∑ _n ∈ bin x N k j, g ((j:ℝ)/k) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ n ∈ bin x N k j, g (Int.fract (x n)) := Finset.sum_le_sum hb
  have hLHS : ∑ j ∈ Finset.range k,
      g ((j:ℝ)/k) * (edf x N (((j:ℝ)+1)/k) - edf x N ((j:ℝ)/k))
      = (∑ j ∈ Finset.range k, ((bin x N k j).card : ℝ) * g ((j:ℝ)/k)) / N := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [edf, edf, ← sub_div, ← card_bin x N k j hk]
    ring
  rw [hLHS, ← sum_bin x g N k hk, div_le_div_iff_of_pos_right hN0]
  exact Finset.sum_le_sum key

/-- Convergence of the upper bin sums. -/
