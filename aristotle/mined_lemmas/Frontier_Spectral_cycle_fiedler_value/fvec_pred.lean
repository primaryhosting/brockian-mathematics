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

lemma fvec_pred (i : Fin (m + 3)) :
    fvec m (i - 1) = Real.cos (2 * Real.pi * (i : ℕ) / ((m + 3 : ℕ) : ℝ)
      - 2 * Real.pi / ((m + 3 : ℕ) : ℝ)) := by
  have hN : ((m + 3 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [fvec_apply m (i - 1) (m + 3 - 1 + (i : ℕ)) (by rw [Fin.sub_def, Fin.val_one])]
  have hc : ((m + 3 - 1 + (i : ℕ) : ℕ) : ℝ) = ((m + 3 : ℕ) : ℝ) - 1 + ((i : ℕ) : ℝ) := by
    have h1 : ((m + 3 - 1 : ℕ) : ℝ) = ((m + 3 : ℕ) : ℝ) - 1 :=
      Nat.cast_sub (by omega) |>.trans (by norm_num)
    push_cast [h1]
    ring
  rw [hc]
  have hsplit : 2 * Real.pi * (((m + 3 : ℕ) : ℝ) - 1 + ((i : ℕ) : ℝ)) / ((m + 3 : ℕ) : ℝ)
      = (2 * Real.pi * ((i : ℕ) : ℝ) / ((m + 3 : ℕ) : ℝ)
        - 2 * Real.pi / ((m + 3 : ℕ) : ℝ)) + 2 * Real.pi := by
    field_simp
    ring
  rw [hsplit, Real.cos_add_two_pi]

