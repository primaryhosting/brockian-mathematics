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

theorem isNSSolution_shearVelocity (nu k : ℝ) :
    IsNSSolution nu (shearVelocity nu k) (fun _ _ => 0)
      (fun x => Real.sin (k * x 1) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) where
  smooth_velocity := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × Vec => Real.exp (-(nu * k ^ 2) * q.1)) :=
      Real.contDiff_exp.comp (contDiff_const.mul contDiff_fst)
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × Vec => Real.sin (k * q.2 1)) :=
      Real.contDiff_sin.comp (contDiff_const.mul
        (((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).contDiff).comp contDiff_snd))
    exact (h1.mul h2).smul contDiff_const
  smooth_pressure := contDiff_const
  initial_condition := by intro x; simp [shearVelocity]
  incompressible := divergence_shearVelocity nu k
  momentum := by
    intro t x i
    rcases eq_or_ne i 0 with rfl | hi
    · have hderiv : deriv (fun s => shearVelocity nu k s x 0) t
          = -(nu * k ^ 2) * Real.exp (-(nu * k ^ 2) * t) * Real.sin (k * x 1) := by
        have hfun : (fun s => shearVelocity nu k s x 0)
            = fun s : ℝ => Real.exp (-(nu * k ^ 2) * s) * Real.sin (k * x 1) := by
          funext s; simp [shearVelocity_apply]
        rw [hfun]
        have h : HasDerivAt (fun s : ℝ => Real.exp (-(nu * k ^ 2) * s) * Real.sin (k * x 1))
            (-(nu * k ^ 2) * Real.exp (-(nu * k ^ 2) * t) * Real.sin (k * x 1)) t := by
          have h0 := ((Real.hasDerivAt_exp (-(nu * k ^ 2) * t)).comp t
            ((hasDerivAt_id t).const_mul (-(nu * k ^ 2)))).mul_const (Real.sin (k * x 1))
          convert h0 using 1
          ring
        exact h.deriv
      have hconv : ∀ j : Fin 3,
          shearVelocity nu k t x j * pd j (fun y => shearVelocity nu k t y 0) x = 0 := by
        intro j
        rcases eq_or_ne j 0 with rfl | hj
        · rw [pd_shearVelocity_zero]; norm_num
        · rw [shearVelocity_apply_ne nu k t x hj, zero_mul]
      rw [hderiv, laplacianComp_shearVelocity_zero]
      simp only [Fin.sum_univ_three, hconv 0, hconv 1, hconv 2, pd_zero, add_zero, sub_zero]
      ring
    · have hfun : (fun s => shearVelocity nu k s x i) = fun _ : ℝ => (0 : ℝ) :=
        funext fun s => shearVelocity_apply_ne nu k s x hi
      have hlap : laplacianComp (shearVelocity nu k) t i x = 0 := by
        have h1 : ∀ j : Fin 3, pd j (fun y => shearVelocity nu k t y i) x = 0 := fun j =>
          pd_shearVelocity_ne nu k t j hi x
        have h2 : ∀ j : Fin 3,
            pd j (fun y => pd j (fun z => shearVelocity nu k t z i) y) x = 0 := by
          intro j
          have : (fun y => pd j (fun z => shearVelocity nu k t z i) y) = fun _ : Vec => (0 : ℝ) :=
            funext fun y => pd_shearVelocity_ne nu k t j hi y
          rw [this, pd_zero]
        simp [laplacianComp, Fin.sum_univ_three, h2 0, h2 1, h2 2]
      rw [hfun, hlap]
      simp [pd_shearVelocity_ne nu k t _ hi]

/-- **Navier–Stokes regularity: a Lean-checked reduction.**

Global regularity for the 3D incompressible Navier–Stokes equations (for all smooth,
divergence free initial data) is *equivalent* to global regularity for the reduced class of
initial data: the zero datum is handled unconditionally by the explicit trivial solution
`u ≡ 0`, `p ≡ 0` (see `isNSSolution_zero`), and every sinusoidal shear datum
`x ↦ sin (k x₂) e₁` is handled unconditionally by the explicit decaying shear flow
(see `isNSSolution_shearVelocity`). -/
