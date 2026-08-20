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

lemma pderiv_eq_zero_of_indep (F : Vec → ℝ) (i : Fin 3) (x : Vec) (h : DifferentiableAt ℝ F x)
    (hindep : ∀ s, F (Function.update x i s) = F x) : pderiv F i x = 0 := by
  have h1 := pderiv_slice F i x h
  have h2 : HasDerivAt (fun s => F (Function.update x i s)) 0 (x i) := by
    have hconst : (fun s => F (Function.update x i s)) = fun _ => F x := funext hindep
    rw [hconst]
    exact hasDerivAt_const _ _
  exact h1.unique h2

/-- A space-time smooth field is smooth, hence differentiable, in the space variable. -/
