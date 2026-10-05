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

private lemma pxx_cosPotential :
    px (px cosPotential) =
      fun x _ => -(Real.cos (2 * Real.pi * x) * (2 * Real.pi)) * (2 * Real.pi) := by
  funext x y
  rw [px, px_cosPotential]
  have hs : HasDerivAt (fun s : ℝ => Real.sin (2 * Real.pi * s))
      (Real.cos (2 * Real.pi * x) * (2 * Real.pi)) x := by
    simpa using (Real.hasDerivAt_sin (2 * Real.pi * x)).comp x
      (by simpa using (hasDerivAt_id x).const_mul (2 * Real.pi))
  exact (hs.neg.mul_const (2 * Real.pi)).deriv

/-- The curved potential `u(x, y) = cos (2πx)` satisfies the hypotheses. -/
