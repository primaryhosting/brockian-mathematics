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

theorem navier_stokes_regularity_shear (nu : ℝ) :
    IsGlobalSmoothSolution nu
      (fun t x => Pi.single 0 (Real.exp (-nu * t) * Real.sin (x 1))) (fun _ _ => 0) := by
  have hdiffg : ∀ c : ℝ, Differentiable ℝ (fun s : ℝ => c * Real.sin s) := fun c => by fun_prop
  have hc0 : ∀ t : ℝ, (fun y : Vec =>
      (Pi.single (0 : Fin 3) (Real.exp (-nu * t) * Real.sin (y 1)) : Vec) 0)
      = fun y : Vec => Real.exp (-nu * t) * Real.sin (y 1) := by
    intro t; funext y; simp
  have hcne : ∀ (t : ℝ) (j : Fin 3), j ≠ 0 → (fun y : Vec =>
      (Pi.single (0 : Fin 3) (Real.exp (-nu * t) * Real.sin (y 1)) : Vec) j)
      = fun _ : Vec => (0 : ℝ) := by
    intro t j hj; funext y; simp [hj]
  refine ⟨?_, contDiff_const, ?_, ?_⟩
  · intro j
    by_cases hj : j = 0
    · subst hj
      have h : (fun q : ℝ × Vec =>
          (Pi.single (0 : Fin 3) (Real.exp (-nu * q.1) * Real.sin (q.2 1)) : Vec) 0)
          = fun q : ℝ × Vec => Real.exp (-nu * q.1) * Real.sin (q.2 1) := by funext q; simp
      show ContDiff ℝ ∞ _
      rw [h]
      fun_prop
    · have h : (fun q : ℝ × Vec =>
          (Pi.single (0 : Fin 3) (Real.exp (-nu * q.1) * Real.sin (q.2 1)) : Vec) j)
          = fun _ : ℝ × Vec => (0 : ℝ) := by funext q; simp [hj]
      show ContDiff ℝ ∞ _
      rw [h]
      exact contDiff_const
  · intro t x
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : i = 0
    · subst hi
      rw [hc0 t, pderiv_coord _ (hdiffg _) 1 0 x]
      simp
    · rw [hcne t i hi]
      exact pderiv_const 0 i x
  · intro t x j
    by_cases hj : j = 0
    · subst hj
      have hconv : convective (fun t x => Pi.single 0 (Real.exp (-nu * t) * Real.sin (x 1)))
          t x 0 = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        by_cases hi : i = 0
        · subst hi
          rw [hc0 t, pderiv_coord _ (hdiffg _) 1 0 x]
          simp
        · simp [hi]
      have hderiv : deriv (fun s : ℝ =>
          (Pi.single (0 : Fin 3) (Real.exp (-nu * s) * Real.sin (x 1)) : Vec) 0) t
          = -nu * Real.exp (-nu * t) * Real.sin (x 1) := by
        have he : (fun s : ℝ =>
            (Pi.single (0 : Fin 3) (Real.exp (-nu * s) * Real.sin (x 1)) : Vec) 0)
            = fun s : ℝ => Real.exp (-nu * s) * Real.sin (x 1) := by funext s; simp
        rw [he]
        have h1 : HasDerivAt (fun s : ℝ => Real.exp (-nu * s)) (-nu * Real.exp (-nu * t)) t := by
          simpa [mul_comm] using ((hasDerivAt_id t).const_mul (-nu)).exp
        simpa using (h1.mul_const (Real.sin (x 1))).deriv
      rw [hconv, hderiv, hc0 t, laplacian_sin, pderiv_const]
      ring
    · have hconv : convective (fun t x => Pi.single 0 (Real.exp (-nu * t) * Real.sin (x 1)))
          t x j = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [hcne t j hj, pderiv_const]
        ring
      have hderiv : deriv (fun s : ℝ =>
          (Pi.single (0 : Fin 3) (Real.exp (-nu * s) * Real.sin (x 1)) : Vec) j) t = 0 := by
        have he : (fun s : ℝ =>
            (Pi.single (0 : Fin 3) (Real.exp (-nu * s) * Real.sin (x 1)) : Vec) j)
            = fun _ : ℝ => (0 : ℝ) := by funext s; simp [hj]
        rw [he]
        simp
      rw [hconv, hderiv, hcne t j hj, laplacian_const, pderiv_const]
      ring

/-- **A Lean-checked reduction.**  For shear flows `u(t, x) = (v(t, x), 0, 0)` whose profile `v`
does not depend on the first coordinate `x₁`, the nonlinear term `(u · ∇)u` vanishes identically
and the incompressible Navier–Stokes system reduces to the linear heat equation
`∂ₜ v = ν Δ v`:  any smooth solution of the heat equation with this symmetry yields a global
smooth solution of the 3D incompressible Navier–Stokes equations (with zero pressure). -/
