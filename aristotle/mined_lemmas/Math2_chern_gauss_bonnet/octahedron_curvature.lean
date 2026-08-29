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

theorem octahedron_curvature (v : Fin 6) : octahedron.curvature v = 1 / 3 := by
  have hN : ∀ s ∈ octahedron.link v, s.card ≤ 2 := by revert v; decide
  obtain ⟨h0, h1, h2⟩ := octahedron_linkFVector v
  rw [octahedron.curvature_eq_linkFVector v 2 hN]
  norm_num [Finset.sum_range_succ, h0, h1, h2]

/-- Gauss–Bonnet made explicit on the octahedral `2`-sphere:
`6 · (1/3) = 2 = χ(S²)`. -/
example : ∑ v ∈ octahedron.vertices, octahedron.curvature v = (octahedron.eulerChar : ℚ) :=
  chern_gauss_bonnet octahedron

