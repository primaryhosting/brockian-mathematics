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

lemma ee_eq_one_iff (a : Fin (m + 3)) : ee m a = 1 ↔ a = 0 := by
  rw [ee, (zeta_primitive m).pow_eq_one_iff_dvd]
  refine ⟨fun h => ?_, by rintro rfl; simp⟩
  have ha := a.isLt
  refine Fin.ext ?_
  rcases Nat.eq_zero_or_pos (a : ℕ) with h0 | h0
  · exact h0
  · exact absurd (Nat.le_of_dvd h0 h) (by omega)

