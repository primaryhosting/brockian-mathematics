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

lemma SmoothST.spatial {v : ℝ → Vec → ℝ} (hv : SmoothST v) (t : ℝ) : Differentiable ℝ (v t) :=
  (hv.comp (contDiff_const.prodMk contDiff_id)).differentiable (by norm_num)

/-- `sin` in one coordinate is an eigenfunction of the Laplacian with eigenvalue `-1`. -/
