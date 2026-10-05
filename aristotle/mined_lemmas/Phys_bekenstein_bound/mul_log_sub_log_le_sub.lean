/-
# Bekenstein Bound
Category: Frontier Phys
Target: Phys.bekenstein_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bekenstein Bound
Category: Frontier Phys
Target: Phys.bekenstein_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open Finset Real

/-- The Bekenstein bound `2 π k R E / (ℏ c)` on the entropy of a system of energy `E`
contained in a sphere of radius `R`. -/

lemma mul_log_sub_log_le_sub {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    p * (Real.log q - Real.log p) ≤ q - p := by
  rcases eq_or_lt_of_le hp with h | hp'
  · simp [← h, hq.le]
  · have hlog : Real.log q - Real.log p = Real.log (q / p) := (Real.log_div hq.ne' hp'.ne').symm
    have h1 : Real.log (q / p) ≤ q / p - 1 := Real.log_le_sub_one_of_pos (div_pos hq hp')
    have h2 : p * Real.log (q / p) ≤ p * (q / p - 1) :=
      mul_le_mul_of_nonneg_left h1 hp'.le
    have h3 : p * (q / p - 1) = q - p := by field_simp
    rw [hlog]
    linarith

/-- Key statistical step: if the "partition function" at inverse temperature `β` is at most
one, then the Shannon entropy of any state is bounded by `β` times its mean energy. -/
