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

lemma pderiv_coord (g : ℝ → ℝ) (hg : Differentiable ℝ g) (k i : Fin 3) (x : Vec) :
    pderiv (fun y => g (y k)) i x = if i = k then deriv g (x k) else 0 := by
  have hp : HasFDerivAt (fun y : Vec => y k) (ContinuousLinearMap.proj k : Vec →L[ℝ] ℝ) x :=
    (ContinuousLinearMap.proj k : Vec →L[ℝ] ℝ).hasFDerivAt
  have h : HasFDerivAt (fun y : Vec => g (y k))
      (deriv g (x k) • (ContinuousLinearMap.proj k : Vec →L[ℝ] ℝ)) x :=
    ((hg (x k)).hasDerivAt).comp_hasFDerivAt x hp
  rw [pderiv, h.fderiv]
  by_cases hik : i = k
  · subst hik; simp
  · simp [hik, Ne.symm hik]

/-- The directional derivative of `F` along the `i`-th axis, seen as an honest one dimensional
derivative along the corresponding coordinate line. -/
