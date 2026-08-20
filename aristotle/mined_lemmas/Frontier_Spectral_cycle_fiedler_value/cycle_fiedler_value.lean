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

theorem cycle_fiedler_value {n : ℕ} (hn : 3 ≤ n) :
    IsLeast {r : ℝ | ∃ x : Fin n → ℝ, x ≠ 0 ∧ (∑ i, x i = 0) ∧
        r = (x ⬝ᵥ ((cycleGraph n).lapMatrix ℝ *ᵥ x)) / (∑ i, x i ^ 2)}
      (2 - 2 * Real.cos (2 * Real.pi / n)) ∧
    IsLeast {μ : ℝ | μ ≠ 0 ∧ ∃ v : Fin n → ℝ, v ≠ 0 ∧
        (cycleGraph n).lapMatrix ℝ *ᵥ v = μ • v}
      (2 - 2 * Real.cos (2 * Real.pi / n)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have hcast : ((m + 3 : ℕ) : ℝ) = (m : ℝ) + 3 := by push_cast; ring
  rw [hcast]
  exact cycle_fiedler_value_aux m

/-- Sanity check: the Fiedler value of the triangle `C 3` is `3`. -/
