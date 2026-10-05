/-
# Navier Stokes Regularity
Category: Frontier — Moonshot
Target: Frontier.navier_stokes_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open ContDiff

namespace Frontier

/-- The physical space `ℝ³`, modelled as `Fin 3 → ℝ`. -/
abbrev Vec := Fin 3 → ℝ

/-- The `i`-th partial derivative of a scalar field on `ℝ³`. -/

theorem isGlobalSmoothSolution_timeShift {ν : ℝ} {u : ℝ → Vec → Vec} {p : ℝ → Vec → ℝ}
    (h : IsGlobalSmoothSolution ν u p) (s : ℝ) :
    IsGlobalSmoothSolution ν (fun t x => u (t + s) x) (fun t x => p (t + s) x) := by
  have hshift : ContDiff ℝ ∞ (fun q : ℝ × Vec => (q.1 + s, q.2)) :=
    (contDiff_fst.add contDiff_const).prodMk contDiff_snd
  refine ⟨h.smooth_velocity.comp hshift, h.smooth_pressure.comp hshift, ?_, ?_⟩
  · intro t x; exact h.incompressible (t + s) x
  · intro t x i
    have hd : deriv (fun r => u (r + s) x i) t = deriv (fun r => u r x i) (t + s) :=
      deriv_comp_add_const (fun r => u r x i) s t
    rw [hd]
    exact h.momentum (t + s) x i

/-- The rest state: for the zero initial velocity the incompressible Navier–Stokes
equations have a global smooth solution (namely `u = 0`, `p = 0`). -/
