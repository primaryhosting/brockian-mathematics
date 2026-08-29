/-
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
open scoped ENNReal NNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math2

open MeasureTheory Filter Topology Set

/-- The Sato–Tate density on `[0, π]`: `θ ↦ (2/π) sin²θ`. -/

lemma empirical_real (θ : ℕ → ℝ) {X : ℕ} (hX : (Nat.primesBelow X).card ≠ 0)
    {s : Set ℝ} (hs : MeasurableSet s) :
    (empirical θ X).real s =
      (((Nat.primesBelow X).filter fun p => θ p ∈ s).card : ℝ) /
        ((Nat.primesBelow X).card : ℝ) := by
  rw [measureReal_def, empirical_apply θ hX hs, ENNReal.toReal_mul]
  simp [div_eq_inv_mul]

