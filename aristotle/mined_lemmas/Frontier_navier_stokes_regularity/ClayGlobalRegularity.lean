import Mathlib

/-!
# Navier Stokes Regularity
Category: Frontier — Moonshot
Target: Frontier.navier_stokes_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` to be the very first command of a
module, so the mandated header comment is placed immediately after the import.
-/

open scoped BigOperators ContDiff

namespace Frontier

namespace NavierStokes

/-- Points/vectors of `ℝ³`. -/
abbrev Vec := Fin 3 → ℝ

/-- The `i`-th partial derivative of a scalar field on `ℝ³`. -/

def ClayGlobalRegularity (nu : ℝ) : Prop :=
  ∀ u₀ : Fin 3 → SchwartzMap Vec ℝ,
    (∀ x, ∑ i, pderiv (fun y => u₀ i y) i x = 0) →
    ∃ u p, IsGlobalSmoothSolution nu u p ∧ (∀ x i, u 0 x i = u₀ i x) ∧
      ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → ∫ x : Vec, ‖u t x‖ ^ 2 ≤ C

/-! ### Basic computations with partial derivatives -/

/-- Partial derivatives of a constant field vanish. -/
