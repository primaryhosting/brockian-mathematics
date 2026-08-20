import Mathlib

/-!
# Cycle Fiedler Value
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

open Finset Matrix

namespace CycleAux

variable (m : ℕ)

/-- The primitive `(m+3)`-rd root of unity. -/

lemma fied_pos : 0 < fied m := by
  rw [fied]
  have hpi := Real.pi_pos
  have hN : (0:ℝ) < ((m + 3 : ℕ) : ℝ) := by positivity
  have h3 : (3:ℝ) ≤ ((m + 3 : ℕ) : ℝ) := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) m]
  have h1 : 0 < 2 * Real.pi / ((m + 3 : ℕ) : ℝ) := by positivity
  have h2 : 2 * Real.pi / ((m + 3 : ℕ) : ℝ) ≤ Real.pi := by
    rw [div_le_iff₀ hN]; nlinarith
  have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl (0:ℝ)) h2 h1
  simp only [Real.cos_zero] at this
  linarith

