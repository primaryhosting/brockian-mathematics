import Mathlib

/-!
# Abstract machinery for paradoxical decompositions

This file develops the general theory needed for the Banach–Tarski paradox, on top of
Mathlib's `Equidecomp` (equidecompositions for a group action).
-/

open Set Function Pointwise

namespace BT

variable {X G H : Type*} [Nonempty X] [Group G] [MulAction G X]

/-- Build an equidecomposition out of a function which is a bijection from `A` to `B` and
moves every point of `A` by an element of a fixed finite set of group elements. -/

theorem exists_cone_equidecomp (f : Equidecomp E O3) (hs : f.source ⊆ S2) (ht : f.target ⊆ S2) :
    ∃ g : Equidecomp E O3, g.source = cone f.source ∧ g.target = cone f.target := by
  classical
  set F : E → E := fun x => ‖x‖ • (f.toPartialEquiv (‖x‖⁻¹ • x)) with hF
  have hFval : ∀ x ∈ cone f.source, ‖F x‖ = ‖x‖ ∧ ‖F x‖⁻¹ • F x = f.toPartialEquiv (‖x‖⁻¹ • x) := by
    intro x hx
    have hx0 : x ≠ 0 := hx.1
    have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
    have h1 : ‖f.toPartialEquiv (‖x‖⁻¹ • x)‖ = 1 :=
      ht (f.toPartialEquiv.map_source hx.2.2)
    have h2 : ‖F x‖ = ‖x‖ := by
      rw [hF]
      simp only
      rw [norm_smul, h1, mul_one, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)]
    refine ⟨h2, ?_⟩
    rw [h2, hF]
    simp only
    rw [smul_smul, inv_mul_cancel₀ hnorm, one_smul]
  refine ⟨mkEquidecomp F (cone f.source) (cone f.target) f.witness ?_ ?_, rfl, rfl⟩
  · intro x hx
    obtain ⟨M, hM, hMx⟩ := f.isDecompOn (‖x‖⁻¹ • x) hx.2.2
    refine ⟨M, hM, ?_⟩
    have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx.1
    show ‖x‖ • (f.toPartialEquiv (‖x‖⁻¹ • x)) = M • x
    rw [show f.toPartialEquiv (‖x‖⁻¹ • x) = M • (‖x‖⁻¹ • x) from hMx, O3.smul_smul_real,
      smul_smul, mul_inv_cancel₀ hnorm, one_smul]
  · refine ⟨?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨h1, h2⟩ := hFval x hx
      refine ⟨?_, ?_, ?_⟩
      · intro hc
        rw [hc, norm_zero] at h1
        exact hx.1 (norm_eq_zero.mp h1.symm)
      · rw [h1]; exact hx.2.1
      · rw [h2]; exact f.toPartialEquiv.map_source hx.2.2
    · intro x hx y hy hxy
      obtain ⟨hx1, hx2⟩ := hFval x hx
      obtain ⟨hy1, hy2⟩ := hFval y hy
      have hnormeq : ‖x‖ = ‖y‖ := by rw [← hx1, ← hy1, hxy]
      have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx.1
      have hval : f.toPartialEquiv (‖x‖⁻¹ • x) = f.toPartialEquiv (‖y‖⁻¹ • y) := by
        rw [← hx2, ← hy2, hxy]
      have hunit : (‖x‖⁻¹ • x) = (‖y‖⁻¹ • y) :=
        f.toPartialEquiv.injOn hx.2.2 hy.2.2 hval
      calc x = ‖x‖ • (‖x‖⁻¹ • x) := by rw [smul_smul, mul_inv_cancel₀ hnorm, one_smul]
        _ = ‖y‖ • (‖y‖⁻¹ • y) := by rw [hunit, hnormeq]
        _ = y := by
            rw [smul_smul, mul_inv_cancel₀ (hnormeq ▸ hnorm), one_smul]
    · intro y hy
      have hy0 : y ≠ 0 := hy.1
      have hnorm : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy0
      set z : E := f.toPartialEquiv.symm (‖y‖⁻¹ • y) with hz
      have hzs : z ∈ f.source := f.toPartialEquiv.map_target hy.2.2
      have hfz : f.toPartialEquiv z = ‖y‖⁻¹ • y := f.toPartialEquiv.right_inv hy.2.2
      have hz1 : ‖z‖ = 1 := hs hzs
      refine ⟨‖y‖ • z, ⟨?_, ?_, ?_⟩, ?_⟩
      · have hzne : z ≠ 0 := by
          intro hc
          rw [hc, norm_zero] at hz1
          exact zero_ne_one hz1
        exact smul_ne_zero hnorm hzne
      · rw [norm_smul, hz1, mul_one, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg y)]
        exact hy.2.1
      · rw [norm_smul, hz1, mul_one, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg y), smul_smul,
          inv_mul_cancel₀ hnorm, one_smul]
        exact hzs
      · show ‖‖y‖ • z‖ • (f.toPartialEquiv (‖‖y‖ • z‖⁻¹ • (‖y‖ • z))) = y
        rw [norm_smul, hz1, mul_one, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg y), smul_smul,
          inv_mul_cancel₀ hnorm, one_smul, hfz, smul_smul, mul_inv_cancel₀ hnorm, one_smul]

/-- Radial extension of a paradoxical decomposition. -/
