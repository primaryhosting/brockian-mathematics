/-
Volume of a wedge of the unit ball of `EuclideanSpace ℝ (Fin 3)` in standard position.

This is an auxiliary file for the Gauss-Bonnet (Girard) theorem for spherical triangles.
-/
import RequestProject.Sector

open MeasureTheory Metric Set Real
open scoped ENNReal

namespace Math

/-- Euclidean 3-space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The wedge of the unit ball cut out by the half-spaces with inner normals
`(1,0,0)` and `(cos t, sin t, 0)`. -/

theorem polar_preimage_planeSector (t : ℝ) (ht0 : 0 ≤ t) (htpi : t ≤ π) (R : ℝ) (hR : 0 ≤ R) :
    (polarCoord.symm ⁻¹' planeSector t R) ∩ polarCoord.target
      = (Ioc (0 : ℝ) R) ×ˢ (Ioo (t - π / 2) (π / 2)) := by
  have hpi := Real.pi_pos
  have htarget : polarCoord.target = (Ioi (0 : ℝ)) ×ˢ (Ioo (-π) π) := rfl
  ext ⟨r, th⟩
  simp only [planeSector, Set.mem_inter_iff, Set.mem_preimage, polarCoord_symm_apply, htarget,
    Set.mem_setOf_eq, Set.mem_prod, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ioi]
  constructor
  · rintro ⟨⟨hnorm, hc1, hc2⟩, hr, hth1, hth2⟩
    have hrpos : 0 < r := hr
    have hcos : 0 < Real.cos th := by nlinarith
    have hc2' : 0 < r * Real.cos (th - t) := by rw [Real.cos_sub]; nlinarith
    have hcos2 : 0 < Real.cos (th - t) := by nlinarith
    have hpyth := Real.sin_sq_add_cos_sq th
    have hupper : th < π / 2 := by
      by_contra hcon
      push_neg at hcon
      have := Real.cos_nonpos_of_pi_div_two_le_of_le hcon (by linarith)
      linarith
    have hlower : -(π / 2) < th := by
      by_contra hcon
      push_neg at hcon
      have := Real.cos_nonpos_of_pi_div_two_le_of_le (x := -th) (by linarith) (by linarith)
      rw [Real.cos_neg] at this
      linarith
    have hr2 : r ^ 2 ≤ R ^ 2 := by nlinarith
    refine ⟨⟨hrpos, by nlinarith⟩, ?_, hupper⟩
    by_contra hcon
    push_neg at hcon
    have := Real.cos_nonpos_of_pi_div_two_le_of_le (x := t - th) (by linarith) (by linarith)
    rw [show t - th = -(th - t) by ring, Real.cos_neg] at this
    linarith
  · rintro ⟨⟨hrpos, hrR⟩, hth1, hth2⟩
    have hcos : 0 < Real.cos th := Real.cos_pos_of_mem_Ioo ⟨by linarith, hth2⟩
    have hcos2 : 0 < Real.cos (th - t) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
    have hpyth := Real.sin_sq_add_cos_sq th
    have hexp : r * Real.cos (th - t)
        = r * Real.cos th * Real.cos t + r * Real.sin th * Real.sin t := by
      rw [Real.cos_sub]; ring
    have hsq : (r * Real.cos th) ^ 2 + (r * Real.sin th) ^ 2 = r ^ 2 := by nlinarith [hpyth]
    exact ⟨⟨by nlinarith, by positivity, by nlinarith⟩, hrpos, by linarith, by linarith⟩

