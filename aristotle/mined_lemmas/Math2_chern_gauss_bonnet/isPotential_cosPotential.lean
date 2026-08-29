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

theorem isPotential_cosPotential : IsPotential cosPotential := by
  constructor
  · intro x y
    show Real.cos (2 * Real.pi * (x + 1)) = Real.cos (2 * Real.pi * x)
    rw [show 2 * Real.pi * (x + 1) = 2 * Real.pi * x + 2 * Real.pi by ring,
      Real.cos_add_two_pi]
  · intro x y; rfl
  · intro y
    exact (Real.differentiable_cos.comp (differentiable_id.const_mul (2 * Real.pi)))
  · intro x; exact differentiable_const _
  · intro y
    rw [px_cosPotential]
    exact ((Real.differentiable_sin.comp
      (differentiable_id.const_mul (2 * Real.pi))).neg).mul_const _
  · intro x
    rw [py_cosPotential]
    exact differentiable_const _
  · rw [pxx_cosPotential]
    fun_prop
  · rw [py_cosPotential]
    simp only [py, deriv_const']
    fun_prop

/-- The curved example really is curved: its Gauss curvature is nonzero at the origin. -/
