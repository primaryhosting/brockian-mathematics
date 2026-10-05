import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib

/-!
# Free Laplacian Essentially Self Adjoint Of Fourier
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.FreeLaplacian2.freeLaplacian_essentiallySelfAdjoint_of_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Complex ComplexInnerProductSpace FourierTransform

noncomputable section

namespace Brockian.Weyl.FreeLaplacian2

/-! ## Essential self-adjointness -/

/-- A (densely defined) operator `T` with domain `D` inside a complex inner product space `H`
is *essentially self-adjoint* when it is densely defined, symmetric, and the ranges of
`T + i` and `T - i` are dense (the basic criterion for essential self-adjointness of a
symmetric operator). -/

lemma exists_mem_multDomain_div (m : α → ℝ) (hm : Measurable m) (s : ℝ) (hs : s ≠ 0)
    (g : Lp ℂ 2 μ) :
    ∃ f : multDomain μ m,
      ⇑(f : Lp ℂ 2 μ) =ᵐ[μ] fun x => ⇑g x / ((m x : ℂ) + (s : ℂ) * Complex.I) := by
  set d : α → ℂ := fun x => (m x : ℂ) + (s : ℂ) * Complex.I with hd
  have hdim : ∀ x, (d x).im = s := by intro x; simp [hd]
  have hdre : ∀ x, (d x).re = m x := by intro x; simp [hd]
  have hdne : ∀ x, d x ≠ 0 := by
    intro x hx
    exact hs (by rw [← hdim x, hx, Complex.zero_im])
  have hnorm_s : ∀ x, |s| ≤ ‖d x‖ := by
    intro x; rw [← hdim x]; exact Complex.abs_im_le_norm (d x)
  have hnorm_m : ∀ x, |m x| ≤ ‖d x‖ := by
    intro x; rw [← hdre x]; exact Complex.abs_re_le_norm (d x)
  have hdmeas : Measurable d := (Complex.measurable_ofReal.comp hm).add measurable_const
  have hmeas : AEStronglyMeasurable (fun x => ⇑g x / d x) μ := by
    simp_rw [div_eq_mul_inv]
    exact (Lp.aestronglyMeasurable g).mul hdmeas.inv.aestronglyMeasurable
  have hsabs : (0 : ℝ) < |s| := abs_pos.2 hs
  have hbound1 : ∀ᵐ x ∂μ, ‖⇑g x / d x‖ ≤ ‖((|s|⁻¹ : ℝ) : ℂ) * ⇑g x‖ := by
    filter_upwards with x
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
      inv_mul_eq_div]
    gcongr
    exact hnorm_s x
  have hmem : MemLp (fun x => ⇑g x / d x) 2 μ :=
    MemLp.mono ((Lp.memLp g).const_mul (((|s|⁻¹ : ℝ) : ℂ))) hmeas hbound1
  have hbound2 : ∀ᵐ x ∂μ, ‖(m x : ℂ) * (⇑g x / d x)‖ ≤ ‖⇑g x‖ := by
    filter_upwards with x
    have h0 : (0 : ℝ) < ‖d x‖ := norm_pos_iff.2 (hdne x)
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, mul_div_assoc',
      div_le_iff₀ h0]
    calc |m x| * ‖⇑g x‖ ≤ ‖d x‖ * ‖⇑g x‖ :=
          mul_le_mul_of_nonneg_right (hnorm_m x) (norm_nonneg _)
      _ = ‖⇑g x‖ * ‖d x‖ := by ring
  have hmem2 : MemLp (fun x => (m x : ℂ) * (⇑g x / d x)) 2 μ :=
    MemLp.mono (Lp.memLp g)
      (((Complex.measurable_ofReal.comp hm).aestronglyMeasurable).mul hmeas) hbound2
  refine ⟨⟨hmem.toLp _, ?_⟩, hmem.coeFn_toLp⟩
  rw [mem_multDomain_iff]
  refine (memLp_congr_ae ?_).2 hmem2
  filter_upwards [hmem.coeFn_toLp] with x hx
  rw [hx]

/-- For `s ≠ 0` real, the operator `M + i s` maps the maximal domain **onto** `L²(μ)`. -/
