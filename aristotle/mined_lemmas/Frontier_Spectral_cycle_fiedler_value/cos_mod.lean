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

lemma cos_mod (k : ℕ) :
    Real.cos (2 * Real.pi * ((k % (m + 3) : ℕ) : ℝ) / ((m + 3 : ℕ) : ℝ))
      = Real.cos (2 * Real.pi * (k : ℝ) / ((m + 3 : ℕ) : ℝ)) := by
  have hN : ((m + 3 : ℕ) : ℝ) ≠ 0 := by positivity
  have hk : (k : ℝ) = ((m + 3 : ℕ) : ℝ) * ((k / (m + 3) : ℕ) : ℝ) + ((k % (m + 3) : ℕ) : ℝ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (Nat.div_add_mod k (m + 3)).symm
  rw [hk]
  have hsplit : 2 * Real.pi * (((m + 3 : ℕ) : ℝ) * ((k / (m + 3) : ℕ) : ℝ)
        + ((k % (m + 3) : ℕ) : ℝ)) / ((m + 3 : ℕ) : ℝ)
      = 2 * Real.pi * ((k % (m + 3) : ℕ) : ℝ) / ((m + 3 : ℕ) : ℝ)
        + ((k / (m + 3) : ℕ) : ℝ) * (2 * Real.pi) := by
    field_simp
    ring
  rw [hsplit, Real.cos_add_nat_mul_two_pi]

