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

theorem gaussCurvature_cosPotential_ne_zero : gaussCurvature cosPotential 0 0 ≠ 0 := by
  have hx : px (px cosPotential) 0 0 = -(4 * Real.pi ^ 2) := by
    rw [pxx_cosPotential]; simp; ring
  have hy : py (py cosPotential) 0 0 = 0 := by
    rw [py_cosPotential]
    simp [py]
  rw [gaussCurvature, hx, hy]
  have hpi : Real.pi ^ 2 > 0 := by positivity
  have hexp : Real.exp (-(2 * cosPotential 0 0)) > 0 := Real.exp_pos _
  nlinarith [hexp, hpi]

/-- Gauss–Bonnet for this curved metric: even though the curvature is not identically zero,
its total integral vanishes. -/
