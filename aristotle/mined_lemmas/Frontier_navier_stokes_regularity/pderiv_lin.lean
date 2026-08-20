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

lemma pderiv_lin (c : Vec) (j : Fin 3) (x : Vec) :
    pderiv (fun y => ∑ k, c k * y k) j x = c j := by
  have hfun : (fun y : Vec => ∑ k, c k * y k) = ∑ k : Fin 3, fun y : Vec => c k * y k := by
    funext y; simp [Finset.sum_apply]
  have h : HasFDerivAt (fun y : Vec => ∑ k, c k * y k)
      (∑ k, (c k) • (ContinuousLinearMap.proj k : Vec →L[ℝ] ℝ)) x := by
    rw [hfun]
    exact HasFDerivAt.sum fun k _ => by
      simpa using ((ContinuousLinearMap.proj k : Vec →L[ℝ] ℝ).hasFDerivAt).const_mul (c k)
  rw [pderiv, h.fderiv]
  simp [Pi.single_apply, Finset.sum_ite_eq']

/-- Partial derivatives of a field depending on a single coordinate. -/
