/-
# Cycle Fiedler Value
Category: Frontier Spectral
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the header above is
-- given as a plain block comment and repeated as a module docstring below.)

import Mathlib

/-!
# Cycle Fiedler Value
Category: Frontier Spectral
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Matrix SimpleGraph Complex ComplexConjugate

namespace Frontier.Spectral

/-! ## A discrete additive character on `ZMod N` -/

section Character

variable {N : ℕ}

/-- The primitive `N`-th root of unity `exp (2πi/N)`. -/

lemma fiedler_pos : 0 < 2 - 2 * Real.cos (2 * Real.pi / ((m : ℝ) + 3)) := by
  have hpi := Real.pi_pos
  have h1 : 0 < 2 * Real.pi / ((m : ℝ) + 3) := by positivity
  have h2 : 2 * Real.pi / ((m : ℝ) + 3) < Real.pi := by
    rw [div_lt_iff₀ (by positivity)]
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  have := (Real.mapsTo_cos_Ioo (Set.mem_Ioo.mpr ⟨h1, h2⟩)).2
  linarith

