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

theorem equidec_cone {A B : Set E} (hA : A ⊆ sph) (hB : B ⊆ sph) (h : Equidec SO3 A B) :
    Equidec SO3 (cone A) (cone B) := by
  classical
  obtain ⟨f, hfs, hft⟩ := h
  refine Equidec.mk' (fun x => ‖x‖ • f (‖x‖⁻¹ • x))
    (fun y => ‖y‖ • f.toPartialEquiv.symm (‖y‖⁻¹ • y)) f.witness ?_ ?_ ?_ ?_ ?_
  · rintro x ⟨hx0, hx1, hxA⟩
    have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hfu : f (‖x‖⁻¹ • x) ∈ B := hft ▸ Equidecomp.apply_mem_target (hfs ▸ hxA)
    exact (cone_radial hB hr hx1 hfu).2.1
  · rintro y ⟨hy0, hy1, hyB⟩
    have hr : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    have hfu : f.toPartialEquiv.symm (‖y‖⁻¹ • y) ∈ A := hfs ▸ Equidecomp.map_target (hft ▸ hyB)
    exact (cone_radial hA hr hy1 hfu).2.1
  · rintro x ⟨hx0, hx1, hxA⟩
    have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hfu : f (‖x‖⁻¹ • x) ∈ B := hft ▸ Equidecomp.apply_mem_target (hfs ▸ hxA)
    obtain ⟨hn, -, -⟩ := cone_radial hB hr hx1 hfu
    show ‖‖x‖ • f (‖x‖⁻¹ • x)‖ • f.toPartialEquiv.symm
      (‖‖x‖ • f (‖x‖⁻¹ • x)‖⁻¹ • (‖x‖ • f (‖x‖⁻¹ • x))) = x
    rw [hn, smul_smul, inv_mul_cancel₀ (ne_of_gt hr), one_smul,
      Equidecomp.left_inv (hfs ▸ hxA), smul_smul, mul_inv_cancel₀ (ne_of_gt hr), one_smul]
  · rintro y ⟨hy0, hy1, hyB⟩
    have hr : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    have hfu : f.toPartialEquiv.symm (‖y‖⁻¹ • y) ∈ A := hfs ▸ Equidecomp.map_target (hft ▸ hyB)
    obtain ⟨hn, -, -⟩ := cone_radial hA hr hy1 hfu
    show ‖‖y‖ • f.toPartialEquiv.symm (‖y‖⁻¹ • y)‖ • f
      (‖‖y‖ • f.toPartialEquiv.symm (‖y‖⁻¹ • y)‖⁻¹ • (‖y‖ • f.toPartialEquiv.symm (‖y‖⁻¹ • y))) = y
    rw [hn, smul_smul, inv_mul_cancel₀ (ne_of_gt hr), one_smul,
      Equidecomp.right_inv (hft ▸ hyB), smul_smul, mul_inv_cancel₀ (ne_of_gt hr), one_smul]
  · rintro x ⟨hx0, hx1, hxA⟩
    obtain ⟨g, hg, hgx⟩ := f.isDecompOn (‖x‖⁻¹ • x) (hfs ▸ hxA)
    refine ⟨g, hg, ?_⟩
    have hr : ‖x‖ ≠ 0 := ne_of_gt (norm_pos_iff.mpr hx0)
    show ‖x‖ • f (‖x‖⁻¹ • x) = g • x
    rw [hgx, so3_smul_smul, smul_smul, mul_inv_cancel₀ hr, one_smul]

