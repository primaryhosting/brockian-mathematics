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

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ContDiff

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-! ## Differential operators on `ℝ³` -/

/-- The `i`-th partial derivative of a scalar field on `ℝ³`. -/

theorem isNSSolution_explicitShear (ν : ℝ) :
    IsNSSolution ν (explicitShear ν) (fun _ _ => 0) := by
  have hsmooth : ContDiff ℝ ∞
      (fun q : ℝ × (Fin 3 → ℝ) => Real.exp (-(ν * q.1)) * Real.sin (q.2 1)) := by
    have h1 : ContDiff ℝ ∞ (fun q : ℝ × (Fin 3 → ℝ) => Real.exp (-(ν * q.1))) :=
      Real.contDiff_exp.comp ((contDiff_const.mul contDiff_fst).neg)
    have h2 : ContDiff ℝ ∞ (fun q : ℝ × (Fin 3 → ℝ) => Real.sin (q.2 1)) :=
      Real.contDiff_sin.comp ((contDiff_apply ℝ ℝ (1 : Fin 3)).comp contDiff_snd)
    exact h1.mul h2
  have hindep : ∀ (t : ℝ) (x : Fin 3 → ℝ) (s : ℝ),
      Real.exp (-(ν * t)) * Real.sin (Function.update x 0 s 1)
        = Real.exp (-(ν * t)) * Real.sin (x 1) := by
    intro t x s
    rw [Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0)]
  have hlap : ∀ (t : ℝ) (x : Fin 3 → ℝ),
      lap (fun y : Fin 3 → ℝ => Real.exp (-(ν * t)) * Real.sin (y 1)) x
        = -(Real.exp (-(ν * t)) * Real.sin (x 1)) := by
    intro t x
    have h0 : (fun y : Fin 3 → ℝ =>
        pderiv 0 (fun z : Fin 3 → ℝ => Real.exp (-(ν * t)) * Real.sin (z 1)) y)
          = fun _ : Fin 3 → ℝ => (0 : ℝ) := by
      funext y
      exact pderiv_eq_zero_of_indep 0 _ y (fun s => hindep t y s)
    have h2 : (fun y : Fin 3 → ℝ =>
        pderiv 2 (fun z : Fin 3 → ℝ => Real.exp (-(ν * t)) * Real.sin (z 1)) y)
          = fun _ : Fin 3 → ℝ => (0 : ℝ) := by
      funext y
      refine pderiv_eq_zero_of_indep 2 _ y (fun s => ?_)
      rw [Function.update_of_ne (by decide : (1 : Fin 3) ≠ 2)]
    have h1 : (fun y : Fin 3 → ℝ =>
        pderiv 1 (fun z : Fin 3 → ℝ => Real.exp (-(ν * t)) * Real.sin (z 1)) y)
          = fun y : Fin 3 → ℝ => Real.exp (-(ν * t)) * Real.cos (y 1) := by
      funext y
      simp [pderiv]
    simp only [lap, Fin.sum_univ_three, h0, h1, h2, pderiv_zero]
    simp [pderiv]
  have hheat : ∀ t : ℝ, 0 ≤ t → ∀ x : Fin 3 → ℝ,
      deriv (fun s : ℝ => Real.exp (-(ν * s)) * Real.sin (x 1)) t
        = ν * lap (fun y : Fin 3 → ℝ => Real.exp (-(ν * t)) * Real.sin (y 1)) x := by
    intro t _ x
    have h : HasDerivAt (fun s : ℝ => Real.exp (-(ν * s))) (Real.exp (-(ν * t)) * -ν) t := by
      simpa using (((hasDerivAt_id t).const_mul ν).neg.exp)
    rw [(h.mul_const (Real.sin (x 1))).deriv, hlap t x]
    ring
  exact isNSSolution_shear ν (fun t x => Real.exp (-(ν * t)) * Real.sin (x 1))
    hsmooth (fun t x s => hindep t x s) hheat

/-- The explicit shear flow is not the zero flow. -/
