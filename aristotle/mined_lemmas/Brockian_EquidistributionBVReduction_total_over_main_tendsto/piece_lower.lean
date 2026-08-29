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

lemma piece_lower (hp : MonotoneOn p (Set.Icc (0:ℝ) 1)) {N k : ℕ} (hk : k < N) :
    p ((k : ℝ) / N) / N ≤ ∫ x in ((k : ℝ) / N)..(((k : ℝ) + 1) / N), p x := by
  have hN : (0 : ℝ) < N := by
    have : 0 < N := lt_of_le_of_lt (Nat.zero_le k) hk
    exact_mod_cast this
  have hle : (k : ℝ) / N ≤ ((k : ℝ) + 1) / N := by gcongr; linarith
  have hmono := intervalIntegral.integral_mono_on (f := fun _ : ℝ => p ((k : ℝ) / N)) (g := p)
    hle intervalIntegrable_const (intervalIntegrable_piece hp hk) ?_
  · rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    have hstep : ((k : ℝ) + 1) / N - (k : ℝ) / N = 1 / N := by field_simp; ring
    rw [hstep] at hmono
    calc p ((k : ℝ) / N) / N = 1 / N * p ((k : ℝ) / N) := by ring
      _ ≤ _ := hmono
  · intro x hx
    have hxmem : x ∈ Set.Icc (0:ℝ) 1 :=
      uIcc_subset_unit hk (by rw [Set.uIcc_of_le hle]; exact hx)
    have hkmem : (k : ℝ) / N ∈ Set.Icc (0:ℝ) 1 :=
      uIcc_subset_unit hk (by rw [Set.uIcc_of_le hle]; exact Set.left_mem_Icc.2 hle)
    exact hp hkmem hxmem hx.1

/-- Upper bound for the integral over one piece, by the right endpoint value. -/
