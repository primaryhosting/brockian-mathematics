import Mathlib

/-!
# Total Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.total_over_main_tendsto
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

open Filter Finset

/-- The `N`-th equidistributed sample sum of `f`: the total of the values of `f` at the
`N` equidistributed sample points `0/N, 1/N, …, (N-1)/N` of the unit interval. -/

lemma piece_upper (hp : MonotoneOn p (Set.Icc (0:ℝ) 1)) {N k : ℕ} (hk : k < N) :
    (∫ x in ((k : ℝ) / N)..(((k : ℝ) + 1) / N), p x) ≤ p (((k : ℝ) + 1) / N) / N := by
  have hN : (0 : ℝ) < N := by
    have : 0 < N := lt_of_le_of_lt (Nat.zero_le k) hk
    exact_mod_cast this
  have hle : (k : ℝ) / N ≤ ((k : ℝ) + 1) / N := by gcongr; linarith
  have hmono := intervalIntegral.integral_mono_on (f := p)
    (g := fun _ : ℝ => p (((k : ℝ) + 1) / N))
    hle (intervalIntegrable_piece hp hk) intervalIntegrable_const ?_
  · rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    have hstep : ((k : ℝ) + 1) / N - (k : ℝ) / N = 1 / N := by field_simp; ring
    rw [hstep] at hmono
    calc (∫ x in ((k : ℝ) / N)..(((k : ℝ) + 1) / N), p x)
        ≤ 1 / N * p (((k : ℝ) + 1) / N) := hmono
      _ = p (((k : ℝ) + 1) / N) / N := by ring
  · intro x hx
    have hxmem : x ∈ Set.Icc (0:ℝ) 1 :=
      uIcc_subset_unit hk (by rw [Set.uIcc_of_le hle]; exact hx)
    have hkmem : ((k : ℝ) + 1) / N ∈ Set.Icc (0:ℝ) 1 :=
      uIcc_subset_unit hk (by rw [Set.uIcc_of_le hle]; exact Set.right_mem_Icc.2 hle)
    exact hp hxmem hkmem hx.2

/-- Left Riemann sums of a monotone function underestimate the integral. -/
