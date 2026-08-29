import Mathlib

/-!
# Config Count Density Of BV
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_density_of_BV
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

namespace Brockian
namespace EquidistributionBVReduction

open Filter Set MeasureTheory
open scoped Topology

/-- `configCount f x N` is the number of the first `N` points of the sequence `x`, each
configuration `x n` being counted with the weight `f (x n)`. -/

lemma sum_bounds (hx : ∀ n, x n ∈ Ico (0:ℝ) 1) (hg : MonotoneOn g (Icc (0:ℝ) 1)) {m : ℕ}
    (hm : 0 < m) (N : ℕ) :
    ∑ i ∈ Finset.range m, g ((i : ℝ) / m) * countIn x m i N
      ≤ ∑ n ∈ Finset.range N, g (x n)
    ∧ ∑ n ∈ Finset.range N, g (x n)
      ≤ ∑ i ∈ Finset.range m, g (((i : ℝ) + 1) / m) * countIn x m i N := by
  simp only [countIn]
  rw [sum_eq_sum_over_intervals hx hm N]
  constructor
  · refine Finset.sum_le_sum (fun i hi => ?_)
    have hi' : i < m := Finset.mem_range.1 hi
    have hbound : ∀ n ∈ (Finset.range N).filter
        (fun n => x n ∈ Ico ((i:ℝ)/m) (((i:ℝ)+1)/m)), g ((i : ℝ) / m) ≤ g (x n) := by
      intro n hn
      have hmem := (Finset.mem_filter.1 hn).2
      exact hg (div_mem_Icc hm (le_of_lt hi')) ⟨(hx n).1, le_of_lt (hx n).2⟩ hmem.1
    have := Finset.card_nsmul_le_sum _ _ _ hbound
    simpa [nsmul_eq_mul, mul_comm] using this
  · refine Finset.sum_le_sum (fun i hi => ?_)
    have hi' : i < m := Finset.mem_range.1 hi
    have hbound : ∀ n ∈ (Finset.range N).filter
        (fun n => x n ∈ Ico ((i:ℝ)/m) (((i:ℝ)+1)/m)), g (x n) ≤ g (((i : ℝ) + 1) / m) := by
      intro n hn
      have hmem := (Finset.mem_filter.1 hn).2
      exact hg ⟨(hx n).1, le_of_lt (hx n).2⟩ (succ_div_mem_Icc hm hi') (le_of_lt hmem.2)
    have := Finset.sum_le_card_nsmul _ _ _ hbound
    simpa [nsmul_eq_mul, mul_comm] using this

