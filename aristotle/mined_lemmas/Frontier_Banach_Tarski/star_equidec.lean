import RequestProject.BT.Ball

/-!
# Banach Tarski
Category: Frontier — Set Theory
Target: Frontier.Banach_Tarski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Metric Set
open scoped Pointwise

namespace Frontier

/-- The vector by which the second copy of the ball is translated. -/

theorem star_equidec {A B : Set E} (hA : A ⊆ S2) (hB : B ⊆ S2)
    (h : Equidec (E ≃ₗᵢ[ℝ] E) A B) : Equidec (E ≃ₗᵢ[ℝ] E) (star A) (star B) := by
  obtain ⟨f, S, hbij, hdec⟩ := h
  refine ⟨fun y => ‖y‖ • f (‖y‖⁻¹ • y), S, ⟨?_, ?_, ?_⟩, ?_⟩
  · rintro y ⟨hy0, hy1, hyA⟩
    have hr : (0 : ℝ) < ‖y‖ := norm_pos_iff.2 hy0
    have hfx : ‖f (‖y‖⁻¹ • y)‖ = 1 := mem_S2.1 (hB (hbij.mapsTo hyA))
    have hnorm : ‖‖y‖ • f (‖y‖⁻¹ • y)‖ = ‖y‖ := by
      rw [norm_smul, hfx, mul_one, Real.norm_eq_abs, abs_of_pos hr]
    show ‖y‖ • f (‖y‖⁻¹ • y) ∈ star B
    refine ⟨?_, ?_, ?_⟩
    · intro hzero
      rw [hzero, norm_zero] at hnorm
      exact hy0 (norm_eq_zero.1 hnorm.symm)
    · rw [hnorm]; exact hy1
    · rw [hnorm, inv_smul_smul₀ (ne_of_gt hr)]
      exact hbij.mapsTo hyA
  · rintro y ⟨hy0, hy1, hyA⟩ z ⟨hz0, hz1, hzA⟩ hyz'
    have hyz : ‖y‖ • f (‖y‖⁻¹ • y) = ‖z‖ • f (‖z‖⁻¹ • z) := hyz'
    have hry : (0 : ℝ) < ‖y‖ := norm_pos_iff.2 hy0
    have hrz : (0 : ℝ) < ‖z‖ := norm_pos_iff.2 hz0
    have hfy : ‖f (‖y‖⁻¹ • y)‖ = 1 := mem_S2.1 (hB (hbij.mapsTo hyA))
    have hfz : ‖f (‖z‖⁻¹ • z)‖ = 1 := mem_S2.1 (hB (hbij.mapsTo hzA))
    have hnorm : ‖y‖ = ‖z‖ := by
      have := congrArg norm hyz
      rwa [norm_smul, norm_smul, hfy, hfz, mul_one, mul_one, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos hry, abs_of_pos hrz] at this
    have hyz2 : ‖z‖ • f (‖y‖⁻¹ • y) = ‖z‖ • f (‖z‖⁻¹ • z) := by
      have hswap : ‖z‖ • f (‖y‖⁻¹ • y) = ‖y‖ • f (‖y‖⁻¹ • y) := by rw [hnorm]
      rw [hswap]; exact hyz
    have hf : f (‖y‖⁻¹ • y) = f (‖z‖⁻¹ • z) := smul_right_injective E (ne_of_gt hrz) hyz2
    have hx : ‖y‖⁻¹ • y = ‖z‖⁻¹ • z := hbij.injOn hyA hzA hf
    have hxx := congrArg (fun v => ‖z‖ • v) hx
    simpa [hnorm, smul_smul, mul_inv_cancel₀ (ne_of_gt hrz)] using hxx
  · rintro z ⟨hz0, hz1, hzB⟩
    have hrz : (0 : ℝ) < ‖z‖ := norm_pos_iff.2 hz0
    obtain ⟨x, hxA, hfx⟩ := hbij.surjOn hzB
    have hxnorm : ‖x‖ = 1 := mem_S2.1 (hA hxA)
    have hnz : ‖‖z‖ • x‖ = ‖z‖ := by
      rw [norm_smul, hxnorm, mul_one, Real.norm_eq_abs, abs_of_pos hrz]
    refine ⟨‖z‖ • x, ⟨?_, ?_, ?_⟩, ?_⟩
    · intro hzero
      rw [hzero, norm_zero] at hnz
      exact hz0 (norm_eq_zero.1 hnz.symm)
    · rw [hnz]; exact hz1
    · rw [hnz, inv_smul_smul₀ (ne_of_gt hrz)]; exact hxA
    · show ‖‖z‖ • x‖ • f (‖‖z‖ • x‖⁻¹ • (‖z‖ • x)) = z
      rw [hnz, inv_smul_smul₀ (ne_of_gt hrz), hfx, smul_inv_smul₀ (ne_of_gt hrz)]
  · rintro y ⟨hy0, hy1, hyA⟩
    have hry : (0 : ℝ) < ‖y‖ := norm_pos_iff.2 hy0
    obtain ⟨g, hgS, hg⟩ := hdec _ hyA
    refine ⟨g, hgS, ?_⟩
    show ‖y‖ • f (‖y‖⁻¹ • y) = g • y
    rw [hg]
    show ‖y‖ • (g (‖y‖⁻¹ • y)) = g y
    rw [map_smul, smul_smul, mul_inv_cancel₀ (ne_of_gt hry), one_smul]

/-- The punctured closed unit ball is paradoxical for the group of linear isometries. -/
