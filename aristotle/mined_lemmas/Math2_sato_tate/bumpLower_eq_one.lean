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

lemma bumpLower_eq_one {α β δ t : ℝ} (hδ : 0 < δ) (h1 : α + δ ≤ t) (h2 : t ≤ β - δ) :
    bumpLower α β δ t = 1 := by
  unfold bumpLower
  have e1 : (1:ℝ) ≤ (t - α) / δ := by rw [le_div_iff₀ hδ]; linarith
  have e2 : (1:ℝ) ≤ (β - t) / δ := by rw [le_div_iff₀ hδ]; linarith
  rw [min_eq_left (le_min e1 e2), max_eq_right zero_le_one]

