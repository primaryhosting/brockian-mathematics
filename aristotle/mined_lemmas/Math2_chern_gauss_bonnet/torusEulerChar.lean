import Mathlib

/-!
# Gauss–Bonnet (the `n = 1` case of Chern–Gauss–Bonnet) for the 2-torus

This file contains a *smooth* instance of the Chern–Gauss–Bonnet theorem, complementing the
combinatorial theorem `Math2.chern_gauss_bonnet` in `RequestProject.Main`.

For a closed oriented surface `M` the Chern–Gauss–Bonnet theorem reads
`∫_M K dA = 2π χ(M)`.  We prove this for the closed even-dimensional manifold
`T² = ℝ²/ℤ²` equipped with an *arbitrary* conformal metric `e^{2u}(dx² + dy²)`, where `u` is
any doubly periodic potential with enough regularity.  For such a metric the Gauss curvature
is `K = -e^{-2u} Δu` and the area density is `e^{2u}`, so the total curvature is `-∫∫ Δu`,
which vanishes by periodicity — in agreement with `χ(T²) = 0`.
-/

namespace Math2.Torus

open MeasureTheory

/-- Partial derivative in the first variable. -/

def torusEulerChar : ℤ := 0

/-- Regularity and periodicity assumptions on the conformal potential `u`: it is `ℤ²`-periodic
(hence defines a metric on the torus `T² = ℝ²/ℤ²`) and has continuous second partial
derivatives.  Every smooth doubly periodic function satisfies these. -/
structure IsPotential (u : ℝ → ℝ → ℝ) : Prop where
  /-- Periodicity in the first variable. -/
  periodic_fst : ∀ x y, u (x + 1) y = u x y
  /-- Periodicity in the second variable. -/
  periodic_snd : ∀ x y, u x (y + 1) = u x y
  /-- Differentiability in the first variable. -/
  diff_fst : ∀ y, Differentiable ℝ fun s => u s y
  /-- Differentiability in the second variable. -/
  diff_snd : ∀ x, Differentiable ℝ fun t => u x t
  /-- Twice differentiability in the first variable. -/
  diff_fst_fst : ∀ y, Differentiable ℝ fun s => px u s y
  /-- Twice differentiability in the second variable. -/
  diff_snd_snd : ∀ x, Differentiable ℝ fun t => py u x t
  /-- Joint continuity of `u_xx`. -/
  cont_fst_fst : Continuous fun p : ℝ × ℝ => px (px u) p.1 p.2
  /-- Joint continuity of `u_yy`. -/
  cont_snd_snd : Continuous fun p : ℝ × ℝ => py (py u) p.1 p.2

variable {u : ℝ → ℝ → ℝ}

