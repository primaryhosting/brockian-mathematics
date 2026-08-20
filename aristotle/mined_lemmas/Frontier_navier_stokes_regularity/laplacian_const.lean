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

lemma laplacian_const (c : ℝ) (x : Vec) : laplacian (fun _ => c) x = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  have h : pderiv (fun _ : Vec => c) i = fun _ => (0 : ℝ) := funext (pderiv_const c i)
  rw [h]
  exact pderiv_const 0 i x

/-- The partial derivatives of a linear functional `y ↦ Σ cₖ yₖ`. -/
