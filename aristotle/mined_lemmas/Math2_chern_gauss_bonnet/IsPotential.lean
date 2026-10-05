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

lemma IsPotential.integral_integral_pxx (hu : IsPotential u) :
    ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, px (px u) x y = 0 := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hswap := MeasureTheory.integral_integral_swap
    (f := fun x y => px (px u) x y) hu.integrableOn_pxx
  simp only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hswap ⊢
  rw [hswap]
  have : ∀ y : ℝ, ∫ x in Set.Ioc (0 : ℝ) 1, px (px u) x y = 0 := by
    intro y
    have := hu.integral_pxx y
    rwa [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at this
  simp [this]

/-- **Gauss–Bonnet for the 2-torus.**  For every conformal metric `e^{2u}(dx² + dy²)` on the
closed surface `T² = ℝ²/ℤ²` (equivalently, every doubly periodic potential `u`), the total
Gauss curvature equals `2π χ(T²) = 0`. -/
