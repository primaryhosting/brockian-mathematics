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

lemma laplacian_sin (c : ℝ) (x : Vec) :
    laplacian (fun y : Vec => c * Real.sin (y 1)) x = -(c * Real.sin (x 1)) := by
  have hg : Differentiable ℝ (fun s : ℝ => c * Real.sin s) := by fun_prop
  have hg' : deriv (fun s : ℝ => c * Real.sin s) = fun s => c * Real.cos s := by funext s; simp
  have hgc : Differentiable ℝ (fun s : ℝ => c * Real.cos s) := by fun_prop
  have hgc' : deriv (fun s : ℝ => c * Real.cos s) = fun s => -(c * Real.sin s) := by
    funext s; simp
  have key1 : pderiv (fun y : Vec => c * Real.sin (y 1)) 1 = fun x : Vec => c * Real.cos (x 1) := by
    funext x; rw [pderiv_coord _ hg 1 1 x, hg']; simp
  have key0 : ∀ i : Fin 3, i ≠ 1 → pderiv (fun y : Vec => c * Real.sin (y 1)) i
      = fun _ : Vec => (0 : ℝ) := by
    intro i hi; funext x; rw [pderiv_coord _ hg 1 i x, if_neg hi]
  rw [laplacian, Finset.sum_eq_single (1 : Fin 3)]
  · rw [key1, pderiv_coord (fun s => c * Real.cos s) hgc 1 1 x, hgc']
    simp
  · intro i _ hi
    rw [key0 i hi]
    exact pderiv_const 0 i x
  · simp

end NavierStokes

open NavierStokes

/-! ### The base case: spatially uniform flows -/

/-- **Base case of global regularity for the 3D incompressible Navier–Stokes equations.**

For every viscosity `ν` and every smooth curve `a : ℝ → ℝ³` there is a globally defined smooth
solution `(u, p)` of the incompressible Navier–Stokes system on all of space-time whose velocity
field is the spatially uniform flow `u(t, x) = a(t)` (the pressure being the linear field
`p(t, x) = - a'(t) · x`).  In particular (taking `a = 0`) the Clay initial datum `u₀ = 0` admits
a global smooth solution. -/
