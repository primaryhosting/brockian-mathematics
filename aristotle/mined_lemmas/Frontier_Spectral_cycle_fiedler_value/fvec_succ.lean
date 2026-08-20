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

lemma fvec_succ (i : Fin (m + 3)) :
    fvec m (i + 1) = Real.cos (2 * Real.pi * (i : ℕ) / ((m + 3 : ℕ) : ℝ)
      + 2 * Real.pi / ((m + 3 : ℕ) : ℝ)) := by
  have hN : ((m + 3 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [fvec_apply m (i + 1) ((i : ℕ) + 1) (by rw [Fin.val_add, Fin.val_one])]
  congr 1
  push_cast
  field_simp

