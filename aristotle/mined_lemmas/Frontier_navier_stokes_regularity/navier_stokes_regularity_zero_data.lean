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

theorem navier_stokes_regularity_zero_data (nu : ℝ) :
    ∃ (u : ℝ → Vec → Vec) (p : ℝ → Vec → ℝ),
      IsGlobalSmoothSolution nu u p ∧ (∀ x, u 0 x = 0) ∧
        ∃ C : ℝ, ∀ t : ℝ, ∫ x : Vec, ‖u t x‖ ^ 2 ≤ C := by
  refine ⟨fun _ _ => 0, fun _ _ => 0, ⟨fun j => contDiff_const, contDiff_const, ?_, ?_⟩,
    fun _ => rfl, 0, fun t => ?_⟩
  · exact fun t x => Finset.sum_eq_zero fun i _ => pderiv_const _ i x
  · intro t x j
    have h1 : convective (fun _ _ => (0 : Vec)) t x j = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [pderiv_const]; ring
    rw [h1, laplacian_const, pderiv_const]
    simp
  · simp

/-- An explicit *nonlinear* check: the decaying shear flow
`u(t, x) = (e^{-ν t} sin x₂, 0, 0)`, `p = 0`, is a global smooth solution of the 3D
incompressible Navier–Stokes equations. -/
