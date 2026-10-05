import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
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

namespace Math2

open Filter Topology Set Polynomial

/-- The Sato–Tate density `(2/π) sin²θ` on the interval `[0, π]`. -/

lemma bumpLower_le_ind {α β δ : ℝ} (hδ : 0 < δ) (t : ℝ) : bumpLower α β δ t ≤ indIcc α β t := by
  unfold indIcc
  split_ifs with h
  · exact bumpLower_le_one _ _ _ _
  · unfold bumpLower
    rcases not_and_or.mp h with h1 | h1
    · have hle : (t - α) / δ ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith [not_le.mp h1]) hδ.le
      rw [max_eq_left]
      exact le_trans (min_le_right _ _) (le_trans (min_le_left _ _) hle)
    · have hle : (β - t) / δ ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith [not_le.mp h1]) hδ.le
      rw [max_eq_left]
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) hle)

