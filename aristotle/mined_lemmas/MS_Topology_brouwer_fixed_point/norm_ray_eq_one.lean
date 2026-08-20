import Mathlib
import Topology.Brouwer

namespace MS.Topology

/-- **Brouwer's fixed point theorem** for the closed unit ball of `EuclideanSpace ℝ (Fin n)`. -/

lemma norm_ray_eq_one {x u : E}
    (hD : 0 ≤ ⟪x, u⟫ ^ 2 + ‖u‖ ^ 2 * (1 - ‖x‖ ^ 2)) (hu : u ≠ 0) :
    ‖x + ((-⟪x, u⟫ + Real.sqrt (⟪x, u⟫ ^ 2 + ‖u‖ ^ 2 * (1 - ‖x‖ ^ 2))) / ‖u‖ ^ 2) • u‖ = 1 := by
  set A := ⟪x, u⟫ with hA
  set Nn := ‖u‖ ^ 2 with hNn
  set Dd := A ^ 2 + Nn * (1 - ‖x‖ ^ 2) with hDd
  have hNpos : 0 < Nn := by rw [hNn]; positivity
  set S := (-A + Real.sqrt Dd) / Nn with hS
  have hsq : Real.sqrt Dd ^ 2 = Dd := Real.sq_sqrt hD
  have h1 : ‖x + S • u‖ ^ 2 = ‖x‖ ^ 2 + 2 * (S * A) + S ^ 2 * Nn := by
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      ← hA, ← hNn]
  have h2 : ‖x‖ ^ 2 + 2 * (S * A) + S ^ 2 * Nn = 1 := by
    rw [hS]; field_simp; linear_combination hsq + hDd
  have h3 : ‖x + S • u‖ ^ 2 = 1 := by rw [h1, h2]
  have h4 : (‖x + S • u‖ - 1) * (‖x + S • u‖ + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp h4 with h | h
  · linarith
  · linarith [norm_nonneg (x + S • u)]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- If `x` already lies on the unit sphere and points away from `u`, the ray does not move it. -/
