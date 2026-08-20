import Mathlib
/-!
# Density Zero Reduction
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.density_zero_reduction
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
namespace BetrothedNumbers

open Filter Finset

/-! ## Natural density -/

/-- The number of elements of `A` in the interval `[1, N]`. -/

lemma sigmaOne_div_eq_sum_inv_divisors {n : ℕ} (hn : 0 < n) :
    (sigmaOne n : ℝ) / n = ∑ d ∈ n.divisors, (1 : ℝ) / d := by
  rw [← Nat.sum_div_divisors n (fun d => (1:ℝ)/d)]
  unfold sigmaOne
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  rw [Nat.mem_divisors] at hd
  obtain ⟨hdvd, _⟩ := hd
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn
  rw [Nat.cast_div_charZero hdvd]
  have : (0:ℝ) < d := by exact_mod_cast hd0
  have : (0:ℝ) < n := by exact_mod_cast hn
  field_simp

/-- The number of multiples of `d` in `[1, N]` is `⌊N/d⌋`. -/
