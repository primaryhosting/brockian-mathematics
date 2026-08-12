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
# Free Laplacian Essentially Self Adjoint Via Plancherel
Category: Brockian (Open Discharge)
Target: Brockian.FreeLaplacianPlancherel.freeLaplacian_essentiallySelfAdjoint_via_plancherel
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Complex
open scoped Real ComplexInnerProductSpace

noncomputable section

namespace Brockian.FreeLaplacianPlancherel

/-! ## Essential self-adjointness -/

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A densely defined symmetric operator `T` with domain `D` in a complex Hilbert space is
*essentially self-adjoint* when both deficiency spaces are trivial, i.e. when the ranges of
`T + i` and `T - i` are dense. -/
def IsEssentiallySelfAdjoint (D : Submodule ℂ H) (T : D →ₗ[ℂ] H) : Prop :=
  Dense (D : Set H) ∧
  (∀ x y : D, ⟪T x, (y : H)⟫ = ⟪(x : H), T y⟫) ∧
  Dense (Set.range fun x : D => T x + Complex.I • (x : H)) ∧
  Dense (Set.range fun x : D => T x - Complex.I • (x : H))

lemma dense_of_orthogonal_trivial [CompleteSpace H] {K : Submodule ℂ H}
    (h : ∀ z : H, (∀ x ∈ K, ⟪x, z⟫ = 0) → z = 0) : Dense (K : Set H) := by
  have hbot : Kᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    exact h z fun x hx => (Submodule.mem_orthogonal K z).mp hz x hx
  have htop : K.topologicalClosure = ⊤ := Submodule.topologicalClosure_eq_top_iff.2 hbot
  have hcl : closure (K : Set H) = Set.univ := by
    have := congrArg (fun S : Submodule ℂ H => (S : Set H)) htop
    simpa [Submodule.topologicalClosure_coe] using this
  exact dense_iff_closure_eq.2 hcl

lemma dense_range_of_orthogonal_trivial [CompleteSpace H] {D : Submodule ℂ H}
    (T : D →ₗ[ℂ] H) (c : ℂ)
    (h : ∀ z : H, (∀ x : D, ⟪T x + c • (x : H), z⟫ = 0) → z = 0) :
    Dense (Set.range fun x : D => T x + c • (x : H)) := by
  have hrange : (Set.range fun x : D => T x + c • (x : H))
      = ((LinearMap.range (T + c • D.subtype) : Submodule ℂ H) : Set H) := by
    rw [LinearMap.coe_range]; rfl
  rw [hrange]
  refine dense_of_orthogonal_trivial (fun z hz => h z fun x => ?_)
  exact hz _ ⟨x, rfl⟩

end Abstract

/-! ## Unitary conjugation -/

section Conjugation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The domain of the operator conjugated by a unitary `U`. -/
def conjDomain (U : H ≃ₗᵢ[ℂ] H) (D : Submodule ℂ H) : Submodule ℂ H :=
  D.comap (U.toLinearEquiv : H →ₗ[ℂ] H)

/-- The conjugate `U⁻¹ T U` of an operator `T` by a unitary `U`. -/
def conjOp (U : H ≃ₗᵢ[ℂ] H) {D : Submodule ℂ H} (T : D →ₗ[ℂ] H) :
    conjDomain U D →ₗ[ℂ] H where
  toFun x := U.symm (T ⟨U (x : H), x.2⟩)
  map_add' x y := by
    have : (⟨U ((x + y : conjDomain U D) : H), (x + y).2⟩ : D)
        = ⟨U (x : H), x.2⟩ + ⟨U (y : H), y.2⟩ := by
      ext; simp
    rw [this, map_add, map_add]
  map_smul' c x := by
    have : (⟨U ((c • x : conjDomain U D) : H), (c • x).2⟩ : D)
        = c • ⟨U (x : H), x.2⟩ := by
      ext; simp
    rw [this, map_smul, map_smul]
    rfl

lemma conjOp_apply (U : H ≃ₗᵢ[ℂ] H) {D : Submodule ℂ H} (T : D →ₗ[ℂ] H)
    (x : conjDomain U D) : conjOp U T x = U.symm (T ⟨U (x : H), x.2⟩) := rfl

lemma inner_symm_left (U : H ≃ₗᵢ[ℂ] H) (a b : H) : ⟪U.symm a, b⟫ = ⟪a, U b⟫ := by
  rw [← U.inner_map_map (U.symm a) b]
  simp

lemma inner_symm_right (U : H ≃ₗᵢ[ℂ] H) (a b : H) : ⟪a, U.symm b⟫ = ⟪U a, b⟫ := by
  rw [← U.inner_map_map a (U.symm b)]
  simp

lemma conjOp_dense_range (U : H ≃ₗᵢ[ℂ] H) {D : Submodule ℂ H} (T : D →ₗ[ℂ] H) (c : ℂ)
    (hd : Dense (Set.range fun x : D => T x + c • (x : H))) :
    Dense (Set.range fun x : conjDomain U D => conjOp U T x + c • (x : H)) := by
  have hset : (Set.range fun x : conjDomain U D => conjOp U T x + c • (x : H))
      = U.symm '' (Set.range fun x : D => T x + c • (x : H)) := by
    ext w
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨T ⟨U (x : H), x.2⟩ + c • (U (x : H)), ⟨⟨U (x : H), x.2⟩, rfl⟩, ?_⟩
      simp [conjOp_apply]
    · rintro ⟨-, ⟨x, rfl⟩, rfl⟩
      have hmem : U.symm (x : H) ∈ conjDomain U D := by
        show U (U.symm (x : H)) ∈ D
        simp
      refine ⟨⟨U.symm (x : H), hmem⟩, ?_⟩
      have hT : T ⟨U (U.symm (x : H)), hmem⟩ = T x := by
        congr 1
        exact Subtype.ext (by simp)
      show U.symm (T ⟨U (U.symm (x : H)), hmem⟩) + c • U.symm (x : H)
          = U.symm (T x + c • (x : H))
      rw [hT]
      simp
  rw [hset]
  exact U.symm.surjective.denseRange.dense_image U.symm.continuous hd

lemma conjOp_essentiallySelfAdjoint (U : H ≃ₗᵢ[ℂ] H) {D : Submodule ℂ H} {T : D →ₗ[ℂ] H}
    (h : IsEssentiallySelfAdjoint D T) :
    IsEssentiallySelfAdjoint (conjDomain U D) (conjOp U T) := by
  obtain ⟨hdense, hsymm, hplus, hminus⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · have himg : ((conjDomain U D : Submodule ℂ H) : Set H) = U.symm '' (D : Set H) := by
      ext w
      constructor
      · intro hw
        exact ⟨U w, hw, by simp⟩
      · rintro ⟨v, hv, rfl⟩
        show U (U.symm v) ∈ D
        simpa using hv
    rw [himg]
    exact U.symm.surjective.denseRange.dense_image U.symm.continuous hdense
  · intro x y
    rw [conjOp_apply, conjOp_apply, inner_symm_left, inner_symm_right]
    exact hsymm ⟨U (x : H), x.2⟩ ⟨U (y : H), y.2⟩
  · exact conjOp_dense_range U T Complex.I hplus
  · have hminus' : Dense (Set.range fun x : D => T x + (-Complex.I) • (x : H)) := by
      simpa [sub_eq_add_neg] using hminus
    have := conjOp_dense_range U T (-Complex.I) hminus'
    simpa [sub_eq_add_neg] using this

end Conjugation

/-! ## The maximal multiplication operator by a real measurable function -/
section Multiplication

variable {X : Type*} [MeasurableSpace X]

section Aux

variable {μ : Measure X}

lemma aeeqfun_mul_add (a b c : X →ₘ[μ] ℂ) : a * (b + c) = a * b + a * c := by
  refine AEEqFun.ext ?_
  filter_upwards [AEEqFun.coeFn_mul a (b + c), AEEqFun.coeFn_add b c,
    AEEqFun.coeFn_add (a * b) (a * c), AEEqFun.coeFn_mul a b, AEEqFun.coeFn_mul a c]
    with x h1 h2 h3 h4 h5
  simp only [h1, h2, h3, h4, h5, Pi.mul_apply, Pi.add_apply]
  ring

lemma aeeqfun_mul_smul (r : ℂ) (a b : X →ₘ[μ] ℂ) : a * (r • b) = r • (a * b) := by
  refine AEEqFun.ext ?_
  filter_upwards [AEEqFun.coeFn_mul a (r • b), AEEqFun.coeFn_smul r b,
    AEEqFun.coeFn_smul r (a * b), AEEqFun.coeFn_mul a b] with x h1 h2 h3 h4
  simp only [h1, h2, h3, h4, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma aeeqfun_mul_zero (a : X →ₘ[μ] ℂ) : a * 0 = 0 := by
  refine AEEqFun.ext ?_
  filter_upwards [AEEqFun.coeFn_mul a 0, AEEqFun.coeFn_zero (β := ℂ) (μ := μ)] with x h1 h2
  simp [h1, h2]

lemma mem_Lp_of_bound {g : X →ₘ[μ] ℂ} {z : Lp ℂ 2 μ}
    (h : ∀ᵐ x ∂μ, ‖(g : X → ℂ) x‖ ≤ ‖z x‖) : g ∈ Lp ℂ 2 μ :=
  Lp.mem_Lp_iff_eLpNorm_lt_top.2 (lt_of_le_of_lt (eLpNorm_mono_ae h) (Lp.eLpNorm_lt_top z))

lemma lp_ext_of_ae_eq {a b : Lp ℂ 2 μ} (h : ⇑a =ᵐ[μ] ⇑b) : a = b :=
  Subtype.ext (AEEqFun.ext h)

/-- If `w` is `z` multiplied by a strictly positive real weight and `w ⟂ z`, then `z = 0`. -/
lemma eq_zero_of_weighted_inner_eq_zero {u : X → ℝ} (z w : Lp ℂ 2 μ)
    (hu : ∀ x, 0 < u x) (hw : ⇑w =ᵐ[μ] fun x => (u x : ℂ) * z x)
    (h : ⟪w, z⟫ = 0) : z = 0 := by
  have hint : Integrable (fun x => (inner ℂ (w x) (z x) : ℂ)) μ := L2.integrable_inner w z
  have heq : (fun x => (inner ℂ (w x) (z x) : ℂ))
      =ᵐ[μ] fun x => ((u x * ‖z x‖ ^ 2 : ℝ) : ℂ) := by
    filter_upwards [hw] with x hx
    rw [hx, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
    have hcomm : z x * ((u x : ℂ) * (starRingEnd ℂ) (z x))
        = (u x : ℂ) * (z x * (starRingEnd ℂ) (z x)) := by ring
    rw [hcomm, Complex.mul_conj']
    push_cast
    ring
  have hGint : Integrable (fun x => u x * ‖z x‖ ^ 2) μ := by
    have h' := (hint.congr heq).re
    simpa only [Complex.ofReal_re] using h'
  have hGzero : ∫ x, u x * ‖z x‖ ^ 2 ∂μ = 0 := by
    have h1 : ∫ x, ((u x * ‖z x‖ ^ 2 : ℝ) : ℂ) ∂μ = 0 := by
      rw [← integral_congr_ae heq, ← L2.inner_def]
      exact h
    rw [integral_complex_ofReal] at h1
    exact_mod_cast h1
  have hnonneg : 0 ≤ fun x => u x * ‖z x‖ ^ 2 := by
    intro x
    have := (hu x).le
    positivity
  have hae := (integral_eq_zero_iff_of_nonneg hnonneg hGint).mp hGzero
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [hae] with x hx
  have hx' : u x * ‖z x‖ ^ 2 = 0 := hx
  rcases mul_eq_zero.mp hx' with h' | h'
  · exact absurd h' (ne_of_gt (hu x))
  · have hzx : ‖z x‖ = 0 := by nlinarith [norm_nonneg (z x)]
    simpa using hzx

end Aux

/-- A real measurable function, viewed as a complex-valued a.e.-equivalence class. -/
def mulSymbol (m : X → ℝ) (hm : Measurable m) (μ : Measure X) : X →ₘ[μ] ℂ :=
  AEEqFun.mk (fun x => (m x : ℂ))
    ((Complex.measurable_ofReal.comp hm).aestronglyMeasurable)

variable (m : X → ℝ) (hm : Measurable m) (μ : Measure X)

lemma coeFn_mulSymbol : ((mulSymbol m hm μ : X →ₘ[μ] ℂ) : X → ℂ) =ᵐ[μ] fun x => (m x : ℂ) :=
  AEEqFun.coeFn_mk _ _

/-- The maximal domain of the multiplication operator by `m` inside `L²(μ)`. -/
def mulDomain : Submodule ℂ (Lp ℂ 2 μ) where
  carrier := {f | mulSymbol m hm μ * (f : X →ₘ[μ] ℂ) ∈ Lp ℂ 2 μ}
  add_mem' := by
    intro a b ha hb
    have h : mulSymbol m hm μ * ((a + b : Lp ℂ 2 μ) : X →ₘ[μ] ℂ)
        = mulSymbol m hm μ * (a : X →ₘ[μ] ℂ) + mulSymbol m hm μ * (b : X →ₘ[μ] ℂ) := by
      rw [show ((a + b : Lp ℂ 2 μ) : X →ₘ[μ] ℂ) = (a : X →ₘ[μ] ℂ) + (b : X →ₘ[μ] ℂ) from rfl,
        aeeqfun_mul_add]
    show mulSymbol m hm μ * ((a + b : Lp ℂ 2 μ) : X →ₘ[μ] ℂ) ∈ Lp ℂ 2 μ
    rw [h]
    exact add_mem ha hb
  zero_mem' := by
    show mulSymbol m hm μ * ((0 : Lp ℂ 2 μ) : X →ₘ[μ] ℂ) ∈ Lp ℂ 2 μ
    rw [show ((0 : Lp ℂ 2 μ) : X →ₘ[μ] ℂ) = 0 from rfl, aeeqfun_mul_zero]
    exact zero_mem _
  smul_mem' := by
    intro c a ha
    have h : mulSymbol m hm μ * ((c • a : Lp ℂ 2 μ) : X →ₘ[μ] ℂ)
        = c • (mulSymbol m hm μ * (a : X →ₘ[μ] ℂ)) := by
      rw [show ((c • a : Lp ℂ 2 μ) : X →ₘ[μ] ℂ) = c • (a : X →ₘ[μ] ℂ) from rfl,
        aeeqfun_mul_smul]
    show mulSymbol m hm μ * ((c • a : Lp ℂ 2 μ) : X →ₘ[μ] ℂ) ∈ Lp ℂ 2 μ
    rw [h]
    exact (c • (⟨_, ha⟩ : Lp ℂ 2 μ)).2

/-- The maximal multiplication operator by the real measurable function `m` on `L²(μ)`. -/
def mulOp : mulDomain m hm μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun f := ⟨mulSymbol m hm μ * (f : X →ₘ[μ] ℂ), f.2⟩
  map_add' f g := by
    apply Subtype.ext
    show mulSymbol m hm μ * ((f : X →ₘ[μ] ℂ) + (g : X →ₘ[μ] ℂ))
        = mulSymbol m hm μ * (f : X →ₘ[μ] ℂ) + mulSymbol m hm μ * (g : X →ₘ[μ] ℂ)
    rw [aeeqfun_mul_add]
  map_smul' c f := by
    apply Subtype.ext
    show mulSymbol m hm μ * (c • (f : X →ₘ[μ] ℂ)) = c • (mulSymbol m hm μ * (f : X →ₘ[μ] ℂ))
    rw [aeeqfun_mul_smul]

lemma coeFn_mulOp (f : mulDomain m hm μ) :
    ⇑(mulOp m hm μ f) =ᵐ[μ] fun x => (m x : ℂ) * (f : Lp ℂ 2 μ) x := by
  have h1 : ⇑(mulOp m hm μ f)
      = ((mulSymbol m hm μ * ((f : Lp ℂ 2 μ) : X →ₘ[μ] ℂ) : X →ₘ[μ] ℂ) : X → ℂ) := rfl
  rw [h1]
  filter_upwards [AEEqFun.coeFn_mul (mulSymbol m hm μ) ((f : Lp ℂ 2 μ) : X →ₘ[μ] ℂ),
    coeFn_mulSymbol m hm μ] with x hx hs
  rw [hx]
  simp [hs]

/-- Given a bounded measurable multiplier `u` such that `m * u` is also bounded, and any
`z ∈ L²`, the product `u * z` lies in the domain of the multiplication operator. -/
lemma exists_mem_mulDomain (u : X → ℂ) (hu : Measurable u) (z : Lp ℂ 2 μ)
    (h1 : ∀ x, ‖u x‖ ≤ 1) (h2 : ∀ x, ‖(m x : ℂ) * u x‖ ≤ 1) :
    ∃ w : mulDomain m hm μ,
      ⇑(w : Lp ℂ 2 μ) =ᵐ[μ] (fun x => u x * z x) ∧
      ⇑(mulOp m hm μ w) =ᵐ[μ] (fun x => (m x : ℂ) * u x * z x) := by
  set g : X →ₘ[μ] ℂ := AEEqFun.mk u hu.aestronglyMeasurable * ((z : Lp ℂ 2 μ) : X →ₘ[μ] ℂ)
    with hg
  have hgcoe : ((g : X →ₘ[μ] ℂ) : X → ℂ) =ᵐ[μ] fun x => u x * z x := by
    rw [hg]
    filter_upwards [AEEqFun.coeFn_mul (AEEqFun.mk u hu.aestronglyMeasurable)
        ((z : Lp ℂ 2 μ) : X →ₘ[μ] ℂ), AEEqFun.coeFn_mk u hu.aestronglyMeasurable] with x hx hu'
    rw [hx]
    simp [hu']
  have hgmem : g ∈ Lp ℂ 2 μ := by
    refine mem_Lp_of_bound (z := z) ?_
    filter_upwards [hgcoe] with x hx
    rw [hx, norm_mul]
    calc ‖u x‖ * ‖z x‖ ≤ 1 * ‖z x‖ := by gcongr; exact h1 x
      _ = ‖z x‖ := one_mul _
  have hmem2 : mulSymbol m hm μ * g ∈ Lp ℂ 2 μ := by
    refine mem_Lp_of_bound (z := z) ?_
    filter_upwards [AEEqFun.coeFn_mul (mulSymbol m hm μ) g, coeFn_mulSymbol m hm μ, hgcoe]
      with x hx hs hz
    rw [hx]
    simp only [Pi.mul_apply, hs, hz]
    rw [← mul_assoc, norm_mul]
    calc ‖(m x : ℂ) * u x‖ * ‖z x‖ ≤ 1 * ‖z x‖ := by gcongr; exact h2 x
      _ = ‖z x‖ := one_mul _
  refine ⟨⟨⟨g, hgmem⟩, hmem2⟩, hgcoe, ?_⟩
  filter_upwards [coeFn_mulOp m hm μ ⟨⟨g, hgmem⟩, hmem2⟩, hgcoe] with x hx hz
  rw [hx]
  show (m x : ℂ) * ((g : X →ₘ[μ] ℂ) : X → ℂ) x = (m x : ℂ) * u x * z x
  rw [hz]
  ring

/-- The multiplication operator by a real function is symmetric. -/
lemma mulOp_symmetric (f g : mulDomain m hm μ) :
    ⟪mulOp m hm μ f, (g : Lp ℂ 2 μ)⟫ = ⟪(f : Lp ℂ 2 μ), mulOp m hm μ g⟫ := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_mulOp m hm μ f, coeFn_mulOp m hm μ g] with x hx hy
  rw [hx, hy, RCLike.inner_apply, RCLike.inner_apply]
  simp only [map_mul, Complex.conj_ofReal]
  ring

lemma mulDomain_dense :
    Dense ((mulDomain m hm μ : Submodule ℂ (Lp ℂ 2 μ)) : Set (Lp ℂ 2 μ)) := by
  refine dense_of_orthogonal_trivial (fun z hz => ?_)
  have hb1 : ∀ x, ‖(((1 + (m x) ^ 2)⁻¹ : ℝ) : ℂ)‖ ≤ 1 := by
    intro x
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg (m x)])
  have hb2 : ∀ x, ‖(m x : ℂ) * (((1 + (m x) ^ 2)⁻¹ : ℝ) : ℂ)‖ ≤ 1 := by
    intro x
    rw [← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (show (0:ℝ) < (1 + (m x) ^ 2)⁻¹ by positivity), mul_comm, ← div_eq_inv_mul,
      div_le_one (by positivity)]
    nlinarith [sq_abs (m x), sq_nonneg (|m x| - 1)]
  obtain ⟨w, hw, -⟩ := exists_mem_mulDomain m hm μ
    (fun x => (((1 + (m x) ^ 2)⁻¹ : ℝ) : ℂ)) (by fun_prop) z hb1 hb2
  exact eq_zero_of_weighted_inner_eq_zero (u := fun x => (1 + (m x) ^ 2)⁻¹) z (w : Lp ℂ 2 μ)
    (fun x => by positivity) hw (hz _ w.2)

lemma mulOp_dense_range (c : ℂ) (hre : c.re = 0) (him : 1 ≤ |c.im|) :
    Dense (Set.range fun f : mulDomain m hm μ => mulOp m hm μ f + c • (f : Lp ℂ 2 μ)) := by
  refine dense_range_of_orthogonal_trivial _ c (fun z hz => ?_)
  have hden : ∀ x, 1 ≤ ‖(m x : ℂ) + c‖ := by
    intro x
    refine him.trans ?_
    have h := Complex.abs_im_le_norm ((m x : ℂ) + c)
    simpa using h
  have hne : ∀ x, ((m x : ℂ) + c) ≠ 0 := by
    intro x hx
    have h := hden x
    rw [hx] at h
    simp at h
    linarith
  have hb1 : ∀ x, ‖((m x : ℂ) + c)⁻¹‖ ≤ 1 := by
    intro x
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ (hden x)
  have hb2 : ∀ x, ‖(m x : ℂ) * ((m x : ℂ) + c)⁻¹‖ ≤ 1 := by
    intro x
    rw [norm_mul, norm_inv, mul_comm, ← div_eq_inv_mul,
      div_le_one (lt_of_lt_of_le zero_lt_one (hden x))]
    have h := Complex.abs_re_le_norm ((m x : ℂ) + c)
    simpa [hre] using h
  obtain ⟨w, hw1, hw2⟩ := exists_mem_mulDomain m hm μ (fun x => ((m x : ℂ) + c)⁻¹)
    (by fun_prop) z hb1 hb2
  have hkey : mulOp m hm μ w + c • (w : Lp ℂ 2 μ) = z := by
    refine lp_ext_of_ae_eq ?_
    filter_upwards [Lp.coeFn_add (mulOp m hm μ w) (c • (w : Lp ℂ 2 μ)),
      Lp.coeFn_smul c (w : Lp ℂ 2 μ), hw1, hw2] with x e1 e2 e3 e4
    rw [e1]
    simp only [Pi.add_apply, e2, Pi.smul_apply, e3, e4, smul_eq_mul]
    have hfac : (m x : ℂ) * ((m x : ℂ) + c)⁻¹ * z x + c * (((m x : ℂ) + c)⁻¹ * z x)
        = (((m x : ℂ) + c) * ((m x : ℂ) + c)⁻¹) * z x := by ring
    rw [hfac, mul_inv_cancel₀ (hne x), one_mul]
  have hzero := hz w
  rw [hkey] at hzero
  exact inner_self_eq_zero.mp hzero

/-- The maximal multiplication operator by a real measurable function is essentially
self-adjoint (in fact self-adjoint). -/
theorem mulOp_essentiallySelfAdjoint :
    IsEssentiallySelfAdjoint (mulDomain m hm μ) (mulOp m hm μ) := by
  refine ⟨mulDomain_dense m hm μ, mulOp_symmetric m hm μ, ?_, ?_⟩
  · exact mulOp_dense_range m hm μ Complex.I (by simp) (by simp)
  · have h := mulOp_dense_range m hm μ (-Complex.I) (by simp) (by simp)
    simpa [sub_eq_add_neg] using h

end Multiplication

/-! ## The free Laplacian -/

section FreeLaplacian

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The Fourier symbol of the free Laplacian `-Δ`: `4π²‖ξ‖²`. -/
def laplacianSymbol : E → ℝ := fun ξ => 4 * π ^ 2 * ‖ξ‖ ^ 2

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma measurable_laplacianSymbol : Measurable (laplacianSymbol E) := by
  unfold laplacianSymbol; fun_prop

/-- The domain of the free Laplacian: the Sobolev space `H²`, described via Plancherel as the
set of `L²` functions whose Fourier transform stays in `L²` after multiplication by `4π²‖ξ‖²`. -/
def freeLaplacianDomain : Submodule ℂ (Lp (α := E) ℂ 2 volume) :=
  conjDomain (Lp.fourierTransformₗᵢ E ℂ)
    (mulDomain (laplacianSymbol E) (measurable_laplacianSymbol E) volume)

/-- The free Laplacian `-Δ` on `L²(E)`, defined via Plancherel as the Fourier conjugate of
multiplication by the symbol `4π²‖ξ‖²`. -/
def freeLaplacian : freeLaplacianDomain E →ₗ[ℂ] Lp (α := E) ℂ 2 volume :=
  conjOp (Lp.fourierTransformₗᵢ E ℂ)
    (mulOp (laplacianSymbol E) (measurable_laplacianSymbol E) volume)

/-- **The free Laplacian is essentially self-adjoint.** -/
theorem freeLaplacian_essentiallySelfAdjoint_via_plancherel :
    IsEssentiallySelfAdjoint (freeLaplacianDomain E) (freeLaplacian E) :=
  conjOp_essentiallySelfAdjoint _ (mulOp_essentiallySelfAdjoint _ _ _)

/-! ### `freeLaplacian` really is `-Δ` on Schwartz functions -/

open SchwartzMap Laplacian LineDeriv FourierTransform

/-- The Fourier transform of a second line derivative is multiplication by `-4π²⟨ξ, v⟩²`. -/
lemma fourier_lineDerivOp_two_apply (f : 𝓢(E, ℂ)) (v ξ : E) :
    𝓕 (∂_{v} (∂_{v} f)) ξ = -(4 * π ^ 2 * (inner ℝ ξ v : ℝ) ^ 2) * 𝓕 f ξ := by
  have hgrow : Function.HasTemperateGrowth (fun x : E => (inner ℝ x v : ℝ)) :=
    ((innerSL ℝ).flip v).hasTemperateGrowth
  rw [fourier_lineDerivOp_eq, fourier_lineDerivOp_eq]
  simp only [SchwartzMap.smul_apply, smulLeftCLM_apply hgrow, Complex.real_smul, smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **Plancherel's formula for the Laplacian**: the Fourier transform of `Δ f` is multiplication
by `-4π²‖ξ‖²`, i.e. by minus the symbol `laplacianSymbol`. -/
lemma fourier_laplacian_apply (f : 𝓢(E, ℂ)) (ξ : E) :
    𝓕 (Δ f) ξ = -(laplacianSymbol E ξ : ℝ) * 𝓕 f ξ := by
  set b := stdOrthonormalBasis ℝ E with hb
  rw [laplacian_eq_sum b f, fourier_sum, SchwartzMap.sum_apply]
  have hsum : ∑ i, (inner ℝ ξ (b i) : ℝ) ^ 2 = ‖ξ‖ ^ 2 := by
    have h := b.sum_inner_mul_inner ξ ξ
    simp only [real_inner_self_eq_norm_sq] at h
    rw [← h]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [sq, real_inner_comm ξ (b i)]
  calc ∑ i, 𝓕 (∂_{b i} (∂_{b i} f)) ξ
      = (-(4 * (π : ℂ) ^ 2) * 𝓕 f ξ) * ∑ i, (((inner ℝ ξ (b i) : ℝ)) : ℂ) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [fourier_lineDerivOp_two_apply E f (b i) ξ]
        ring
    _ = (-(4 * (π : ℂ) ^ 2) * 𝓕 f ξ) * ((‖ξ‖ ^ 2 : ℝ) : ℂ) := by
        rw [← hsum]
        push_cast
        ring
    _ = -(laplacianSymbol E ξ : ℝ) * 𝓕 f ξ := by
        simp only [laplacianSymbol]
        push_cast
        ring

/-- Multiplying the Fourier transform of a Schwartz function by the symbol `4π²‖ξ‖²` gives the
Fourier transform of `-Δ f`. -/
lemma mulSymbol_mul_fourier_toLp (f : 𝓢(E, ℂ)) :
    mulSymbol (laplacianSymbol E) (measurable_laplacianSymbol E) volume *
        (((𝓕 f).toLp 2 volume : Lp (α := E) ℂ 2 volume) : E →ₘ[volume] ℂ)
      = (((𝓕 (-(Δ f))).toLp 2 volume : Lp (α := E) ℂ 2 volume) : E →ₘ[volume] ℂ) := by
  refine AEEqFun.ext ?_
  filter_upwards [AEEqFun.coeFn_mul (mulSymbol (laplacianSymbol E) (measurable_laplacianSymbol E)
      volume) (((𝓕 f).toLp 2 volume : Lp (α := E) ℂ 2 volume) : E →ₘ[volume] ℂ),
    coeFn_mulSymbol (laplacianSymbol E) (measurable_laplacianSymbol E) volume,
    SchwartzMap.coeFn_toLp (𝓕 f) 2 volume,
    SchwartzMap.coeFn_toLp (𝓕 (-(Δ f))) 2 volume] with ξ h1 h2 h3 h4
  rw [h1]
  simp only [Pi.mul_apply, h2, h3, h4]
  rw [show (𝓕 (-(Δ f)) : 𝓢(E, ℂ)) = -(𝓕 (Δ f)) from fourier_neg _, SchwartzMap.neg_apply,
    fourier_laplacian_apply]
  ring

lemma schwartz_mem_freeLaplacianDomain (f : 𝓢(E, ℂ)) :
    (f.toLp 2 volume : Lp (α := E) ℂ 2 volume) ∈ freeLaplacianDomain E := by
  show mulSymbol (laplacianSymbol E) (measurable_laplacianSymbol E) volume *
      ((Lp.fourierTransformₗᵢ E ℂ (f.toLp 2 volume) : Lp (α := E) ℂ 2 volume) :
        E →ₘ[volume] ℂ) ∈ Lp ℂ 2 volume
  have hF : (Lp.fourierTransformₗᵢ E ℂ (f.toLp 2 volume) : Lp (α := E) ℂ 2 volume)
      = (𝓕 f).toLp 2 volume := SchwartzMap.toLp_fourier_eq f
  rw [hF, mulSymbol_mul_fourier_toLp]
  exact ((𝓕 (-(Δ f))).toLp 2 volume).2

/-- On Schwartz functions, the operator defined via Plancherel is the classical `-Δ`. -/
theorem freeLaplacian_apply_schwartz (f : 𝓢(E, ℂ)) :
    freeLaplacian E ⟨f.toLp 2 volume, schwartz_mem_freeLaplacianDomain E f⟩
      = (-(Δ f)).toLp 2 volume := by
  have hF : (Lp.fourierTransformₗᵢ E ℂ (f.toLp 2 volume) : Lp (α := E) ℂ 2 volume)
      = (𝓕 f).toLp 2 volume := SchwartzMap.toLp_fourier_eq f
  have h1 : mulOp (laplacianSymbol E) (measurable_laplacianSymbol E) volume
      ⟨Lp.fourierTransformₗᵢ E ℂ (f.toLp 2 volume),
        (schwartz_mem_freeLaplacianDomain E f)⟩
      = (𝓕 (-(Δ f))).toLp 2 volume := by
    apply Subtype.ext
    show mulSymbol (laplacianSymbol E) (measurable_laplacianSymbol E) volume *
        ((Lp.fourierTransformₗᵢ E ℂ (f.toLp 2 volume) : Lp (α := E) ℂ 2 volume) :
          E →ₘ[volume] ℂ) = _
    rw [hF, mulSymbol_mul_fourier_toLp]
  have h2 : ((𝓕 (-(Δ f))).toLp 2 volume : Lp (α := E) ℂ 2 volume)
      = Lp.fourierTransformₗᵢ E ℂ ((-(Δ f)).toLp 2 volume) :=
    (SchwartzMap.toLp_fourier_eq (-(Δ f))).symm
  show (Lp.fourierTransformₗᵢ E ℂ).symm (mulOp (laplacianSymbol E)
    (measurable_laplacianSymbol E) volume ⟨Lp.fourierTransformₗᵢ E ℂ (f.toLp 2 volume), _⟩) = _
  rw [h1, h2, LinearIsometryEquiv.symm_apply_apply]

end FreeLaplacian

end Brockian.FreeLaplacianPlancherel

