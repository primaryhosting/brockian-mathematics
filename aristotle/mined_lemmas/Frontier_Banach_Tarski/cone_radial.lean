/-
Absorbing the countable set of poles: the unit sphere is `SO(3)`-paradoxical.
-/
import RequestProject.Sphere

open Matrix Set Pointwise

namespace BT

noncomputable section

/-! ### Countability of the solution sets of rotation equations -/

/-- For a point `d` off the `z`-axis, only countably many angles `t` satisfy
`rZ (c * t) • d = d'`. -/

theorem cone_radial {T : Set E} (hT : T ⊆ sph) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    {v : E} (hv : v ∈ T) :
    ‖r • v‖ = r ∧ r • v ∈ cone T ∧ ‖r • v‖⁻¹ • (r • v) = v := by
  have hv1 : ‖v‖ = 1 := hT hv
  have hnorm : ‖r • v‖ = r := by
    rw [norm_smul, hv1, mul_one, Real.norm_eq_abs, abs_of_pos hr]
  have hlast : ‖r • v‖⁻¹ • (r • v) = v := by
    rw [hnorm, smul_smul, inv_mul_cancel₀ (ne_of_gt hr), one_smul]
  refine ⟨hnorm, ⟨?_, by rw [hnorm]; exact hr1, by rw [hlast]; exact hv⟩, hlast⟩
  intro hc
  rw [hc, norm_zero] at hnorm
  exact (ne_of_gt hr) hnorm.symm

