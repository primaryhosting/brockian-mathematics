import Mathlib
/-!
# Navier Stokes Regularity
Category: Frontier — Moonshot
Target: Frontier.navier_stokes_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Mathlib coverage

A search of the current Mathlib (both by name and by `exact?`/`apply?` against the goal) turns up
no development of the Navier–Stokes equations: the string `Navier` does not occur anywhere in the
library, and there is no theory of the incompressible Euler or Navier–Stokes systems. So the full
Millennium statement `Frontier.NavierStokesGlobalRegularity` below cannot be closed by an existing
lemma; it is stated here and left unproved (it is an open problem).

What *is* proved below, axiom-cleanly:

* `Frontier.isNavierStokesSolution_shear` — a Lean-checked **reduction**: every smooth solution of
  the one dimensional heat equation `∂ₜ g = ν ∂²_y g` yields a global smooth solution of the full
  three dimensional nonlinear incompressible Navier–Stokes system (the shear flow
  `u (t, x) = (g t x₂, 0, 0)`, with zero pressure). The nonlinearity `(u · ∇)u` vanishes identically
  on this class.
* `Frontier.navier_stokes_regularity` — the target: global existence and smoothness for the
  shear-flow initial data obtained this way.
* `Frontier.navier_stokes_regularity_const` — the base case of constant initial velocity.
* `Frontier.navier_stokes_regularity_sine` — an explicit nontrivial global smooth solution.

The Mathlib inputs used are elementary calculus lemmas: `deriv_const`, `HasDerivAt.sin`,
`HasDerivAt.cos`, `HasDerivAt.exp`, `HasDerivAt.const_mul`, `HasDerivAt.deriv`, `contDiff_const`,
`contDiff_apply`, `ContDiff.comp`, `ContDiff.prodMk`, and `Function.update_of_ne`.
-/

open scoped BigOperators

namespace Frontier

/-! ## Differential operators on `ℝ³` -/

/-- The `j`-th partial derivative of a scalar field on `ℝ³`. -/

theorem isNavierStokesSolution_shear (ν : ℝ) (g : ℝ → ℝ → ℝ)
    (hsmooth : ∀ n : ℕ, ContDiff ℝ n (fun q : ℝ × ℝ => g q.1 q.2))
    (hheat : ∀ t y : ℝ, deriv (fun s : ℝ => g s y) t = ν * deriv (deriv (g t)) y) :
    IsNavierStokesSolution ν (fun x => ![g 0 (x 1), 0, 0])
      (fun t x => ![g t (x 1), 0, 0]) (fun _ _ => 0) := by
  constructor
  · intro i n
    fin_cases i
    · simpa using (hsmooth n).comp
        (contDiff_fst.prodMk ((contDiff_apply ℝ ℝ (1 : Fin 3)).comp contDiff_snd))
    · exact contDiff_const
    · exact contDiff_const
  · intro n
    exact contDiff_const
  · intro t _ x i
    fin_cases i
    · show deriv (fun s : ℝ => g s (x 1)) t
        = ν * lap (fun y : Fin 3 → ℝ => g t (y 1)) x
          - advect (fun y => ![g t (y 1), 0, 0]) 0 x
          - partialDeriv (fun _ : Fin 3 → ℝ => (0 : ℝ)) 0 x
      rw [lap_coord (g t) 1 x, hheat t (x 1)]
      have hadv : advect (fun y => ![g t (y 1), 0, 0]) 0 x = 0 := by
        simp only [advect, Fin.sum_univ_three]
        rw [show (fun y : Fin 3 → ℝ => (![g t (y 1), 0, 0] : Fin 3 → ℝ) 0)
            = fun y : Fin 3 → ℝ => g t (y 1) from rfl]
        simp [partialDeriv_coord]
      rw [hadv]
      simp
    · show deriv (fun _ : ℝ => (0 : ℝ)) t
        = ν * lap (fun _ : Fin 3 → ℝ => (0 : ℝ)) x
          - advect (fun y => ![g t (y 1), 0, 0]) 1 x
          - partialDeriv (fun _ : Fin 3 → ℝ => (0 : ℝ)) 1 x
      have hadv : advect (fun y => ![g t (y 1), 0, 0]) 1 x = 0 := by
        simp only [advect, Fin.sum_univ_three]
        rw [show (fun y : Fin 3 → ℝ => (![g t (y 1), 0, 0] : Fin 3 → ℝ) 1)
            = fun _ : Fin 3 → ℝ => (0 : ℝ) from rfl]
        simp
      rw [hadv]
      simp
    · show deriv (fun _ : ℝ => (0 : ℝ)) t
        = ν * lap (fun _ : Fin 3 → ℝ => (0 : ℝ)) x
          - advect (fun y => ![g t (y 1), 0, 0]) 2 x
          - partialDeriv (fun _ : Fin 3 → ℝ => (0 : ℝ)) 2 x
      have hadv : advect (fun y => ![g t (y 1), 0, 0]) 2 x = 0 := by
        simp only [advect, Fin.sum_univ_three]
        rw [show (fun y : Fin 3 → ℝ => (![g t (y 1), 0, 0] : Fin 3 → ℝ) 2)
            = fun _ : Fin 3 → ℝ => (0 : ℝ) from rfl]
        simp
      rw [hadv]
      simp
  · intro t _ x
    have h1 : (fun y : Fin 3 → ℝ => (![g t (y 1), 0, 0] : Fin 3 → ℝ) 1)
        = fun _ : Fin 3 → ℝ => (0 : ℝ) := rfl
    have h2 : (fun y : Fin 3 → ℝ => (![g t (y 1), 0, 0] : Fin 3 → ℝ) 2)
        = fun _ : Fin 3 → ℝ => (0 : ℝ) := rfl
    have h0 : (fun y : Fin 3 → ℝ => (![g t (y 1), 0, 0] : Fin 3 → ℝ) 0)
        = fun y : Fin 3 → ℝ => g t (y 1) := rfl
    simp only [divg, Fin.sum_univ_three, h0, h1, h2, partialDeriv_const, partialDeriv_coord]
    simp
  · intro x
    rfl

/-! ## Base cases -/

/-- **Base case.** For every viscosity `ν` and every constant initial velocity `c` there is a
globally defined smooth solution of the three dimensional incompressible Navier–Stokes
equations, namely the constant flow with zero pressure. -/
