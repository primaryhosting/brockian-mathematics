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

lemma ind_le_bumpUpper {α β δ : ℝ} (hδ : 0 < δ) (t : ℝ) : indIcc α β t ≤ bumpUpper α β δ t := by
  unfold indIcc
  split_ifs with h
  · have h1 : (1:ℝ) ≤ (t - (α - δ)) / δ := by rw [le_div_iff₀ hδ]; linarith [h.1]
    have h2 : (1:ℝ) ≤ ((β + δ) - t) / δ := by rw [le_div_iff₀ hδ]; linarith [h.2]
    unfold bumpUpper
    rw [min_eq_left (le_min h1 h2), max_eq_right zero_le_one]
  · exact bumpUpper_nonneg _ _ _ _

