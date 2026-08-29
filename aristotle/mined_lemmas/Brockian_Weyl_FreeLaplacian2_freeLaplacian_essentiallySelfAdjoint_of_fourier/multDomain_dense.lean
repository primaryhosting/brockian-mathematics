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

lemma multDomain_dense (m : α → ℝ) (hm : Measurable m) :
    Dense ((multDomain μ m : Submodule ℂ (Lp ℂ 2 μ)) : Set (Lp ℂ 2 μ)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro h hh
  set e : α → ℂ := fun x => (m x : ℂ) - Complex.I with he
  have heim : ∀ x, (e x).im = -1 := by intro x; simp [he]
  have hene : ∀ x, e x ≠ 0 := by
    intro x hx
    have := heim x
    rw [hx, Complex.zero_im] at this
    norm_num at this
  have henorm : ∀ x, (1 : ℝ) ≤ ‖e x‖ := by
    intro x
    have h1 : |(e x).im| ≤ ‖e x‖ := Complex.abs_im_le_norm (e x)
    rw [heim x] at h1
    simpa using h1
  have hemeas : Measurable e := (Complex.measurable_ofReal.comp hm).sub measurable_const
  have hmeas : AEStronglyMeasurable (fun x => ⇑h x / e x) μ := by
    simp_rw [div_eq_mul_inv]
    exact (Lp.aestronglyMeasurable h).mul hemeas.inv.aestronglyMeasurable
  have hu : MemLp (fun x => ⇑h x / e x) 2 μ := by
    refine MemLp.mono (Lp.memLp h) hmeas ?_
    filter_upwards with x
    rw [norm_div]
    exact div_le_self (norm_nonneg _) (henorm x)
  set u : Lp ℂ 2 μ := hu.toLp _ with hudef
  have key : ∀ g : Lp ℂ 2 μ, ⟪g, u⟫ = 0 := by
    intro g
    obtain ⟨f, hf⟩ := exists_mem_multDomain_div m hm 1 one_ne_zero g
    have h0 : ⟪(f : Lp ℂ 2 μ), h⟫ = 0 := (Submodule.mem_orthogonal _ _).1 hh _ f.2
    rw [L2.inner_def] at h0 ⊢
    rw [← h0]
    apply integral_congr_ae
    filter_upwards [hf, hu.coeFn_toLp] with x hx hy
    rw [hx, hy, RCLike.inner_apply', RCLike.inner_apply']
    have hd1 : ((m x : ℂ) + ((1 : ℝ) : ℂ) * Complex.I) = (m x : ℂ) + Complex.I := by simp
    rw [hd1, map_div₀]
    have hconj : (starRingEnd ℂ) ((m x : ℂ) + Complex.I) = e x := by
      simp [he, Complex.conj_ofReal, sub_eq_add_neg]
    rw [hconj]
    field_simp
  have hzero : u = 0 := by
    have := key u
    rwa [inner_self_eq_zero] at this
  rw [Lp.ext_iff]
  have hz : (fun x => ⇑h x / e x) =ᵐ[μ] (0 : α → ℂ) := by
    refine hu.coeFn_toLp.symm.trans ?_
    rw [← hudef, hzero]
    exact Lp.coeFn_zero ℂ 2 μ
  filter_upwards [hz, Lp.coeFn_zero (E := ℂ) (p := 2) (μ := μ)] with x hx hx0
  rw [hx0]
  rcases div_eq_zero_iff.1 hx with h1 | h1
  · exact h1
  · exact absurd h1 (hene x)

/-- Multiplication by a real measurable function is essentially self-adjoint on its
maximal domain in `L²(μ)`. -/
