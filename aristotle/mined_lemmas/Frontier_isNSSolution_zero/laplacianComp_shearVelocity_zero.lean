/-
# Navier Stokes Regularity
Category: Frontier — Moonshot
Target: Frontier.navier_stokes_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Navier Stokes Regularity
Category: Frontier — Moonshot
Target: Frontier.navier_stokes_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open scoped BigOperators

/-- Physical space `ℝ³`. -/
abbrev Vec := EuclideanSpace ℝ (Fin 3)

/-- The `i`-th partial derivative of a scalar field on `ℝ³`. -/

lemma laplacianComp_shearVelocity_zero (nu k t : ℝ) (x : Vec) :
    laplacianComp (shearVelocity nu k) t 0 x
      = Real.exp (-(nu * k ^ 2) * t) * (-(k ^ 2) * Real.sin (k * x 1)) := by
  have hzero : ∀ j : Fin 3, j ≠ 1 →
      pd j (fun y => pd j (fun z => shearVelocity nu k t z 0) y) x = 0 := by
    intro j hj
    have : (fun y => pd j (fun z => shearVelocity nu k t z 0) y) = fun _ : Vec => (0 : ℝ) := by
      funext y; rw [pd_shearVelocity_zero]; simp [hj]
    rw [this, pd_zero]
  have hone : pd 1 (fun y => pd 1 (fun z => shearVelocity nu k t z 0) y) x
      = Real.exp (-(nu * k ^ 2) * t) * (-(k ^ 2) * Real.sin (k * x 1)) := by
    have hfun : (fun y : Vec => pd 1 (fun z => shearVelocity nu k t z 0) y)
        = fun y : Vec => (fun s : ℝ => Real.exp (-(nu * k ^ 2) * t) * (k * Real.cos (k * s))) (y 1) := by
      funext y; rw [pd_shearVelocity_zero]; simp
    rw [hfun, pd_coord 1 1 _ (differentiable_shear_profile' _ _) x, deriv_shear_profile']
    simp
  simp [laplacianComp, Fin.sum_univ_three, hone, hzero 0 (by decide), hzero 2 (by decide)]

/-- **A nontrivial exact global solution.**  For every viscosity `ν` and every wave number `k`
the viscously decaying shear flow `u(t,x) = (e^{-ν k² t} sin (k x₂), 0, 0)` with zero pressure
is a globally defined smooth solution of the Navier–Stokes equations. -/
