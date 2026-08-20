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

/-
# Free Laplacian Essentially Self Adjoint Of Fourier
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.FreeLaplacian2.freeLaplacian_essentiallySelfAdjoint_of_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

-- Note: Lean requires `import` commands to come before any module docstring `/-! ... -/`, so the
-- required header appears verbatim at the very top of the file as a block comment and is repeated
-- here, after the import, as the module docstring.

/-!
# Free Laplacian Essentially Self Adjoint Of Fourier
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.FreeLaplacian2.freeLaplacian_essentiallySelfAdjoint_of_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


/-!
The free Laplacian `-Δ`, defined on the Schwartz space `𝓢(ℝ^d, ℂ)` regarded as a dense
subspace of `L²(ℝ^d, ℂ)`, is essentially self-adjoint.

The proof follows the classical "basic criterion" of von Neumann/Weyl:

* an abstract criterion (`essentiallySelfAdjoint_of_dense_shift_ranges`): a densely defined
  symmetric operator whose deficiency ranges `Ran (T ± i)` are dense is essentially
  self-adjoint;
* the Fourier transform turns `-Δ` on Schwartz space into multiplication by
  `ξ ↦ 4π²‖ξ‖²` (`fourier_negLaplacianS`), and dividing a smooth compactly supported
  function by `4π²‖ξ‖² ± i` (which never vanishes) produces again a smooth compactly
  supported function.  Since smooth compactly supported functions are dense in `L²` and
  the Fourier transform is unitary on `L²` (Plancherel), the deficiency ranges are dense.
-/

open MeasureTheory SchwartzMap Filter LinearPMap
open scoped FourierTransform ComplexInnerProductSpace LinearPMap Laplacian LineDeriv Topology
  ContDiff

noncomputable section

namespace Brockian.Weyl.FreeLaplacian2

/-! ## An abstract criterion for essential self-adjointness -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The operator `T + c` on the domain of the partially defined operator `T`. -/
def shiftMap (T : E →ₗ.[ℂ] E) (c : ℂ) : T.domain →ₗ[ℂ] E := T.toFun + c • T.domain.subtype

omit [CompleteSpace E] in
@[simp] lemma shiftMap_apply (T : E →ₗ.[ℂ] E) (c : ℂ) (x : T.domain) :
    shiftMap T c x = T x + c • (x : E) := rfl

/-- A densely defined operator on a Hilbert space is *essentially self-adjoint* if its adjoint
is self-adjoint; equivalently, if its closure `T††` is self-adjoint. -/
def EssentiallySelfAdjoint (T : E →ₗ.[ℂ] E) : Prop := IsSelfAdjoint T†

theorem eq_zero_of_dense_shift_range {T : E →ₗ.[ℂ] E} (hT : Dense (T.domain : Set E)) {c : ℂ}
    (hd : Dense ((LinearMap.range (shiftMap T c) : Submodule ℂ E) : Set E))
    (y : T†.domain) (hy : T† y = -(starRingEnd ℂ c) • (y : E)) : (y : E) = 0 := by
  refine hd.eq_zero_of_inner_left ?_
  rintro ⟨-, ⟨x, rfl⟩⟩
  have hfa : T†.IsFormalAdjoint T := LinearPMap.adjoint_isFormalAdjoint hT
  have h1 : ⟪T† y, (x : E)⟫ = ⟪(y : E), T x⟫ := hfa y x
  simp only [shiftMap_apply, inner_add_right, inner_smul_right]
  rw [← h1, hy]
  simp [inner_smul_left]

theorem dense_adjoint_domain {T : E →ₗ.[ℂ] E} (hT : Dense (T.domain : Set E))
    (hsym : T.IsFormalAdjoint T) : Dense ((T†).domain : Set E) :=
  hT.mono (by exact_mod_cast (LinearPMap.IsFormalAdjoint.le_adjoint hT hsym).1)

theorem adjoint_adjoint_le {T : E →ₗ.[ℂ] E} (hT : Dense (T.domain : Set E))
    (hsym : T.IsFormalAdjoint T) : T†† ≤ T† := by
  have hle : T ≤ T† := LinearPMap.IsFormalAdjoint.le_adjoint hT hsym
  have hT' : Dense ((T†).domain : Set E) := dense_adjoint_domain hT hsym
  have hfa : (T††).IsFormalAdjoint (T†) := LinearPMap.adjoint_isFormalAdjoint hT'
  have hmem : ∀ y : (T††).domain, ∀ x : T.domain, ⟪T†† y, (x : E)⟫ = ⟪(y : E), T x⟫ := by
    intro y x
    have hx : (x : E) ∈ (T†).domain := hle.1 x.2
    rw [hfa y ⟨(x : E), hx⟩]
    congr 1
    exact (hle.2 rfl).symm
  refine ⟨fun y hy => ?_, ?_⟩
  · exact LinearPMap.mem_adjoint_domain_of_exists _ ⟨T†† ⟨y, hy⟩, hmem ⟨y, hy⟩⟩
  · rintro ⟨y, hy⟩ ⟨y', hy'⟩ h
    simp only at h
    subst h
    exact (LinearPMap.adjoint_apply_eq hT _ (hmem ⟨y, hy⟩)).symm

omit [CompleteSpace E] in
theorem inner_apply_self_im {T : E →ₗ.[ℂ] E} (hsym : T.IsFormalAdjoint T) (x : T.domain) :
    (⟪T x, (x : E)⟫).im = 0 := by
  have h : ⟪T x, (x : E)⟫ = ⟪(x : E), T x⟫ := hsym x x
  rw [← inner_conj_symm (x : E)] at h
  exact Complex.conj_eq_iff_im.mp h.symm

omit [CompleteSpace E] in
theorem norm_shift_sq {T : E →ₗ.[ℂ] E} (hsym : T.IsFormalAdjoint T) {c : ℂ} (hc : c.re = 0)
    (x : T.domain) : ‖shiftMap T c x‖ ^ 2 = ‖T x‖ ^ 2 + ‖c‖ ^ 2 * ‖(x : E)‖ ^ 2 := by
  have him := inner_apply_self_im hsym x
  rw [shiftMap_apply, norm_add_sq (𝕜 := ℂ)]
  have h1 : ⟪T x, c • (x : E)⟫ = c * ⟪T x, (x : E)⟫ := by rw [inner_smul_right]
  have h2 : RCLike.re ⟪T x, c • (x : E)⟫ = 0 := by
    rw [h1]
    show (c * ⟪T x, (x : E)⟫).re = 0
    rw [Complex.mul_re, hc, him]; ring
  rw [h2, norm_smul]
  ring

theorem cauchySeq_of_dist_le {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    {f : ℕ → α} {g : ℕ → β} (h : ∀ m n, dist (f m) (f n) ≤ dist (g m) (g n))
    (hg : CauchySeq g) : CauchySeq f := by
  rw [Metric.cauchySeq_iff] at hg ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hg ε hε
  exact ⟨N, fun m hm n hn => lt_of_le_of_lt (h m n) (hN m hm n hn)⟩

theorem exists_mem_closure_graph {T : E →ₗ.[ℂ] E} (hsym : T.IsFormalAdjoint T) {c : ℂ}
    (hc : c.re = 0) (hc1 : ‖c‖ = 1)
    (hd : Dense ((LinearMap.range (shiftMap T c) : Submodule ℂ E) : Set E)) (u : E) :
    ∃ p : E × E, p ∈ closure (T.graph : Set (E × E)) ∧ p.2 + c • p.1 = u := by
  have hbound : ∀ a b : T.domain, ‖(a : E) - (b : E)‖ ≤ ‖shiftMap T c a - shiftMap T c b‖ ∧
      ‖T a - T b‖ ≤ ‖shiftMap T c a - shiftMap T c b‖ := by
    intro a b
    have hkey : ‖shiftMap T c (a - b)‖ ^ 2
        = ‖T (a - b)‖ ^ 2 + ‖c‖ ^ 2 * ‖((a - b : T.domain) : E)‖ ^ 2 := norm_shift_sq hsym hc _
    rw [hc1] at hkey
    have h1 : ((a - b : T.domain) : E) = (a : E) - b := rfl
    have h2 : T (a - b) = T a - T b := LinearPMap.map_sub T a b
    have h3 : shiftMap T c (a - b) = shiftMap T c a - shiftMap T c b := map_sub _ a b
    rw [h1, h2, h3] at hkey
    constructor
    · nlinarith [norm_nonneg (T a - T b), norm_nonneg ((a : E) - b),
        norm_nonneg (shiftMap T c a - shiftMap T c b)]
    · nlinarith [norm_nonneg (T a - T b), norm_nonneg ((a : E) - b),
        norm_nonneg (shiftMap T c a - shiftMap T c b)]
  have hu : u ∈ closure (Set.range (shiftMap T c)) := by
    have := hd u
    rwa [LinearMap.coe_range] at this
  rw [mem_closure_iff_seq_limit] at hu
  obtain ⟨g, hg, hgu⟩ := hu
  choose x hx using hg
  have hgc : CauchySeq g := hgu.cauchySeq
  have hxc : CauchySeq (fun n => ((x n : E))) := by
    refine cauchySeq_of_dist_le (g := g) (fun m n => ?_) hgc
    rw [dist_eq_norm, dist_eq_norm, ← hx m, ← hx n]
    exact (hbound (x m) (x n)).1
  have hTxc : CauchySeq (fun n => (T (x n))) := by
    refine cauchySeq_of_dist_le (g := g) (fun m n => ?_) hgc
    rw [dist_eq_norm, dist_eq_norm, ← hx m, ← hx n]
    exact (hbound (x m) (x n)).2
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hxc
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hTxc
  refine ⟨(a, v), ?_, ?_⟩
  · refine mem_closure_of_tendsto (ha.prodMk_nhds hv) ?_
    filter_upwards with n
    exact T.mem_graph (x n)
  · have hlim : Tendsto (fun n => T (x n) + c • ((x n : E))) atTop (𝓝 (v + c • a)) :=
      hv.add (ha.const_smul c)
    have h2 : (fun n => T (x n) + c • ((x n : E))) = g := funext fun n => hx n
    rw [h2] at hlim
    exact tendsto_nhds_unique hlim hgu

/-- **Basic criterion for essential self-adjointness.**  A densely defined symmetric operator
on a complex Hilbert space whose deficiency ranges `Ran (T + i)` and `Ran (T - i)` are dense
is essentially self-adjoint. -/
theorem essentiallySelfAdjoint_of_dense_shift_ranges {T : E →ₗ.[ℂ] E}
    (hT : Dense (T.domain : Set E)) (hsym : T.IsFormalAdjoint T)
    (hplus : Dense ((LinearMap.range (shiftMap T Complex.I) : Submodule ℂ E) : Set E))
    (hminus : Dense ((LinearMap.range (shiftMap T (-Complex.I)) : Submodule ℂ E) : Set E)) :
    EssentiallySelfAdjoint T := by
  have hT' : Dense ((T†).domain : Set E) := dense_adjoint_domain hT hsym
  have h1 : T†† ≤ T† := adjoint_adjoint_le hT hsym
  have hTle2 : T ≤ T†† :=
    LinearPMap.IsFormalAdjoint.le_adjoint hT' (LinearPMap.adjoint_isFormalAdjoint hT)
  have hsub : closure (T.graph : Set (E × E)) ⊆ ((T††).graph : Set (E × E)) := by
    refine (LinearPMap.adjoint_isClosed hT').closure_subset_iff.mpr ?_
    exact_mod_cast LinearPMap.le_graph_of_le hTle2
  have key : ∀ y : (T†).domain, ∃ h : (y : E) ∈ (T††).domain, T†† ⟨(y : E), h⟩ = T† y := by
    intro y
    obtain ⟨p, hp, hpu⟩ := exists_mem_closure_graph hsym (c := -Complex.I) (by simp) (by simp)
      hminus (T† y + (-Complex.I) • (y : E))
    have hpg : p ∈ (T††).graph := hsub hp
    rw [LinearPMap.mem_graph_iff] at hpg
    obtain ⟨z, hz1, hz2⟩ := hpg
    have hz1' : (z : E) ∈ (T†).domain := h1.1 z.2
    have hz2' : T† ⟨(z : E), hz1'⟩ = p.2 := by
      rw [← hz2]; exact (h1.2 rfl).symm
    have hwval : T† (y - (⟨(z : E), hz1'⟩ : (T†).domain)) = Complex.I • ((y : E) - (z : E)) := by
      rw [LinearPMap.map_sub, hz2', hz1]
      have hp2 : p.2 = T† y + (-Complex.I) • (y : E) - (-Complex.I) • p.1 := by
        rw [← hpu]; module
      rw [hp2]
      module
    have hzero : ((y - (⟨(z : E), hz1'⟩ : (T†).domain) : (T†).domain) : E) = 0 := by
      refine eq_zero_of_dense_shift_range hT hplus _ ?_
      rw [hwval]
      simp only [Submodule.coe_sub]
      simp
    simp only [Submodule.coe_sub] at hzero
    have hyz : (y : E) = (z : E) := sub_eq_zero.mp hzero
    refine ⟨by rw [hyz]; exact z.2, ?_⟩
    have hzz : (⟨(y : E), by rw [hyz]; exact z.2⟩ : (T††).domain) = z := by
      ext; exact hyz
    rw [hzz, hz2, ← hz2']
    congr 1
    ext
    exact hyz.symm
  have h2 : T† ≤ T†† := by
    refine ⟨fun y hy => (key ⟨y, hy⟩).1, ?_⟩
    rintro ⟨y, hy⟩ ⟨y', hy'⟩ h
    simp only at h
    subst h
    exact ((key ⟨y, hy⟩).2).symm
  exact le_antisymm h1 h2

end Abstract

/-! ## The free Laplacian on `L²(ℝ^d)` -/

/-- Euclidean space `ℝ^d`. -/
abbrev Euc (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The Hilbert space `L²(ℝ^d, ℂ)`. -/
abbrev L2 (d : ℕ) := Lp (α := Euc d) ℂ 2 volume

variable (d : ℕ)

/-- The inclusion of Schwartz functions into `L²`. -/
def toL2 : 𝓢(Euc d, ℂ) →ₗ[ℂ] L2 d := (SchwartzMap.toLpCLM ℂ ℂ 2 volume).toLinearMap

theorem toL2_injective : Function.Injective (toL2 d) :=
  SchwartzMap.injective_toLp (F := ℂ) 2 (volume : Measure (Euc d))

/-- The free Laplacian `-Δ` acting on Schwartz functions. -/
def negLaplacianS : 𝓢(Euc d, ℂ) →L[ℂ] 𝓢(Euc d, ℂ) :=
  -(LineDeriv.laplacianCLM ℂ (Euc d) 𝓢(Euc d, ℂ))

theorem negLaplacianS_eq (f : 𝓢(Euc d, ℂ)) : negLaplacianS d f = -(Δ f) := by
  simp [negLaplacianS]

/-- `negLaplacianS` really is the pointwise operator `f ↦ -Δf`. -/
theorem negLaplacianS_apply (f : 𝓢(Euc d, ℂ)) (x : Euc d) :
    negLaplacianS d f x = -(Δ (f : Euc d → ℂ) x) := by
  rw [negLaplacianS_eq]
  simp [SchwartzMap.laplacian_apply]

/-- The free Laplacian `-Δ` as an unbounded operator on `L²(ℝ^d, ℂ)` with domain the
(image of the) Schwartz space. -/
def freeLaplacian : L2 d →ₗ.[ℂ] L2 d where
  domain := LinearMap.range (toL2 d)
  toFun := (toL2 d) ∘ₗ (negLaplacianS d).toLinearMap ∘ₗ
    ((LinearEquiv.ofInjective (toL2 d) (toL2_injective d)).symm : _ →ₗ[ℂ] 𝓢(Euc d, ℂ))

theorem mem_domain_freeLaplacian (f : 𝓢(Euc d, ℂ)) : toL2 d f ∈ (freeLaplacian d).domain :=
  ⟨f, rfl⟩

theorem freeLaplacian_apply (f : 𝓢(Euc d, ℂ)) (h : toL2 d f ∈ (freeLaplacian d).domain) :
    freeLaplacian d ⟨toL2 d f, h⟩ = toL2 d (negLaplacianS d f) := by
  show (toL2 d) ((negLaplacianS d) ((LinearEquiv.ofInjective (toL2 d) (toL2_injective d)).symm
    ⟨toL2 d f, h⟩)) = _
  congr 2
  exact (LinearEquiv.ofInjective (toL2 d) (toL2_injective d)).symm_apply_eq.mpr rfl

theorem dense_domain_freeLaplacian :
    Dense (((freeLaplacian d).domain : Submodule ℂ (L2 d)) : Set (L2 d)) := by
  show Dense ((LinearMap.range (toL2 d) : Submodule ℂ (L2 d)) : Set (L2 d))
  rw [LinearMap.coe_range]
  exact SchwartzMap.denseRange_toLpCLM (F := ℂ) (p := 2) (by norm_num) (μ := volume)

/-! ### Symmetry -/

theorem inner_toL2 (f g : 𝓢(Euc d, ℂ)) :
    ⟪toL2 d f, toL2 d g⟫ = ∫ x, ⟪f x, g x⟫ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [SchwartzMap.coeFn_toLp f 2 (volume : Measure (Euc d)),
    SchwartzMap.coeFn_toLp g 2 (volume : Measure (Euc d))] with x hx hy
  show ⟪((toL2 d f : L2 d) : Euc d → ℂ) x, ((toL2 d g : L2 d) : Euc d → ℂ) x⟫ = _
  rw [show ((toL2 d f : L2 d) : Euc d → ℂ) x = f x from hx,
    show ((toL2 d g : L2 d) : Euc d → ℂ) x = g x from hy]

theorem freeLaplacian_isSymmetric : (freeLaplacian d).IsFormalAdjoint (freeLaplacian d) := by
  rintro ⟨-, ⟨f, rfl⟩⟩ ⟨-, ⟨g, rfl⟩⟩
  rw [freeLaplacian_apply, freeLaplacian_apply, inner_toL2, inner_toL2]
  simp only [negLaplacianS_eq]
  have key := SchwartzMap.integral_bilinear_laplacian_right_eq_left
    (μ := (volume : Measure (Euc d))) f g
    ((ContinuousLinearMap.mul ℝ ℂ).comp (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap)
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.mul_apply',
    ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply] at key
  simp only [SchwartzMap.neg_apply, RCLike.inner_apply', _root_.map_neg, neg_mul, mul_neg,
    integral_neg, key]

/-! ### The Fourier multiplier -/

/-- The symbol of the free Laplacian: `ξ ↦ 4π²‖ξ‖²`. -/
def symbol (ξ : Euc d) : ℂ := ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ)

theorem symbol_contDiff : ContDiff ℝ ∞ (symbol d) := by
  have h1 : ContDiff ℝ ∞ (fun ξ : Euc d => ‖ξ‖ ^ 2) := contDiff_norm_sq ℝ
  have h2 : symbol d = fun ξ : Euc d => ((4 * Real.pi ^ 2 : ℝ) : ℂ) * ((‖ξ‖ ^ 2 : ℝ) : ℂ) := by
    funext ξ; simp [symbol]
  rw [h2]
  exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp h1)

/-- The Fourier transform of a directional derivative. -/
theorem fourier_lineDeriv_apply (f : 𝓢(Euc d, ℂ)) (m ξ : Euc d) :
    (𝓕 (∂_{m} f)) ξ = (2 * Real.pi * Complex.I) * ((inner ℝ ξ m : ℝ) : ℂ) * (𝓕 f) ξ := by
  rw [SchwartzMap.fourier_lineDerivOp_eq]
  have htg : (inner ℝ · m : Euc d → ℝ).HasTemperateGrowth := by fun_prop
  simp [SchwartzMap.smulLeftCLM_apply_apply htg]
  ring_nf

/-- The Fourier transform turns `-Δ` into multiplication by `4π²‖ξ‖²`. -/
theorem fourier_negLaplacianS (f : 𝓢(Euc d, ℂ)) (ξ : Euc d) :
    (𝓕 (negLaplacianS d f)) ξ = symbol d ξ * (𝓕 f) ξ := by
  set b := stdOrthonormalBasis ℝ (Euc d) with hb
  have hlap : Δ f = ∑ i, ∂_{b i} (∂_{b i} f) := SchwartzMap.laplacian_eq_sum b f
  have hneg : 𝓕 (negLaplacianS d f) = -(𝓕 (Δ f : 𝓢(Euc d, ℂ))) := by
    rw [negLaplacianS_eq]
    exact map_neg (SchwartzMap.fourierTransformCLM ℂ) _
  have hsum : 𝓕 (Δ f : 𝓢(Euc d, ℂ)) = ∑ i, 𝓕 (∂_{b i} (∂_{b i} f)) := by
    rw [hlap]
    exact map_sum (SchwartzMap.fourierTransformCLM ℂ) _ _
  rw [hneg]
  simp only [SchwartzMap.neg_apply, hsum, SchwartzMap.sum_apply]
  have hterm : ∀ i, (𝓕 (∂_{b i} (∂_{b i} f))) ξ
      = -((2 * (Real.pi : ℂ)) ^ 2 * ((inner ℝ ξ (b i) : ℝ) : ℂ) ^ 2) * (𝓕 f) ξ := by
    intro i
    rw [fourier_lineDeriv_apply, fourier_lineDeriv_apply]
    ring_nf
    simp [Complex.I_sq]
  simp only [hterm]
  rw [← Finset.sum_mul]
  have hnorm : ∑ i, ((inner ℝ ξ (b i) : ℝ) : ℂ) ^ 2 = ((‖ξ‖ ^ 2 : ℝ) : ℂ) := by
    have hbb := b.sum_inner_mul_inner (𝕜 := ℝ) ξ ξ
    have h2 : ∑ i, (inner ℝ ξ (b i) : ℝ) ^ 2 = ‖ξ‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← hbb]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [real_inner_comm (b i) ξ]
      ring
    rw [← h2]
    push_cast
    ring
  have hs : (∑ i, -((2 * (Real.pi : ℂ)) ^ 2 * ((inner ℝ ξ (b i) : ℝ) : ℂ) ^ 2))
      = -((2 * (Real.pi : ℂ)) ^ 2 * ((‖ξ‖ ^ 2 : ℝ) : ℂ)) := by
    rw [← hnorm, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [hs, symbol]
  push_cast
  ring

theorem fourier_injective : ∀ u v : 𝓢(Euc d, ℂ), 𝓕 u = 𝓕 v → u = v := by
  intro u v huv
  have h : 𝓕⁻ (𝓕 u) = 𝓕⁻ (𝓕 v) := by rw [huv]
  rwa [FourierTransform.fourierInv_fourier_eq, FourierTransform.fourierInv_fourier_eq] at h

/-! ### Density of the deficiency ranges -/

theorem dense_smooth_compactSupport :
    Dense {u : L2 d | ∃ g : 𝓢(Euc d, ℂ), HasCompactSupport (g : Euc d → ℂ) ∧ u = toL2 d g} := by
  intro f
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall).2 fun ε hε ↦ ?_
  obtain ⟨g, hg₁, hg₂, hg₃⟩ := MeasureTheory.MemLp.exist_eLpNorm_sub_le
    (p := 2) (by norm_num) (by norm_num) (Lp.memLp f) hε
  refine ⟨toL2 d (hg₁.toSchwartzMap hg₂), ⟨hg₁.toSchwartzMap hg₂, hg₁, rfl⟩, ?_⟩
  have hae : (f : Euc d → ℂ) - (((hg₁.toSchwartzMap hg₂).toLp 2 (volume : Measure (Euc d))
        : L2 d) : Euc d → ℂ) =ᶠ[ae (volume : Measure (Euc d))] (f : Euc d → ℂ) - g := by
    filter_upwards [(hg₁.toSchwartzMap hg₂).coeFn_toLp 2 (volume : Measure (Euc d))]
    simp
  show dist (toL2 d (hg₁.toSchwartzMap hg₂)) f ≤ ε
  rw [dist_comm]
  simp only [Lp.dist_def]
  show (eLpNorm ((f : Euc d → ℂ) - (((hg₁.toSchwartzMap hg₂).toLp 2 (volume : Measure (Euc d))
        : L2 d) : Euc d → ℂ)) 2 volume).toReal ≤ ε
  rw [eLpNorm_congr_ae hae]
  calc (eLpNorm ((f : Euc d → ℂ) - g) 2 volume).toReal ≤ (ENNReal.ofReal ε).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hg₃
    _ = ε := ENNReal.toReal_ofReal hε.le

/-- Given a smooth compactly supported `g` and `c` with `symbol d ξ + c ≠ 0` for all `ξ`, the
equation `(-Δ + c) f = 𝓕⁻¹ g` has a Schwartz solution: divide by the symbol on the Fourier
side, which preserves smoothness and compact support. -/
theorem exists_solution {c : ℂ} (hc : ∀ ξ : Euc d, symbol d ξ + c ≠ 0) (g : 𝓢(Euc d, ℂ))
    (hg : HasCompactSupport (g : Euc d → ℂ)) :
    ∃ f : 𝓢(Euc d, ℂ), negLaplacianS d f + c • f = 𝓕⁻ g := by
  set φfun : Euc d → ℂ := fun ξ => (symbol d ξ + c)⁻¹ * g ξ with hφfun
  have hcs : HasCompactSupport φfun := HasCompactSupport.mul_left hg
  have hcd : ContDiff ℝ ∞ φfun :=
    (((symbol_contDiff d).add contDiff_const).inv hc).mul g.smooth'
  set φ : 𝓢(Euc d, ℂ) := hcs.toSchwartzMap hcd with hφ
  refine ⟨𝓕⁻ φ, ?_⟩
  have hFφ : 𝓕 (𝓕⁻ φ) = φ := FourierTransform.fourier_fourierInv_eq φ
  apply fourier_injective
  rw [FourierTransform.fourier_fourierInv_eq g]
  have hlin : 𝓕 (negLaplacianS d (𝓕⁻ φ) + c • (𝓕⁻ φ))
      = 𝓕 (negLaplacianS d (𝓕⁻ φ)) + c • 𝓕 (𝓕⁻ φ) := by simp
  rw [hlin, hFφ]
  ext ξ
  rw [SchwartzMap.add_apply, fourier_negLaplacianS, hFφ, SchwartzMap.smul_apply]
  have hφval : φ ξ = (symbol d ξ + c)⁻¹ * g ξ := rfl
  rw [hφval]
  simp only [smul_eq_mul]
  have hstep : symbol d ξ * ((symbol d ξ + c)⁻¹ * g ξ) + c * ((symbol d ξ + c)⁻¹ * g ξ)
      = ((symbol d ξ + c) * (symbol d ξ + c)⁻¹) * g ξ := by ring
  rw [hstep, mul_inv_cancel₀ (hc ξ), one_mul]

theorem dense_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) {s : Set X} (hs : Dense s) : Dense (h '' s) := by
  rw [dense_iff_closure_eq, ← Homeomorph.image_closure, hs.closure_eq, Set.image_univ,
    h.surjective.range_eq]

theorem dense_shift_range {c : ℂ} (hc : ∀ ξ : Euc d, symbol d ξ + c ≠ 0) :
    Dense ((LinearMap.range (shiftMap (freeLaplacian d) c) : Submodule ℂ (L2 d)) : Set (L2 d)) := by
  set e : L2 d ≃ₗᵢ[ℂ] L2 d := (MeasureTheory.Lp.fourierTransformₗᵢ (Euc d) ℂ).symm with he
  have himg := dense_image_homeomorph e.toHomeomorph (dense_smooth_compactSupport d)
  refine himg.mono ?_
  rintro - ⟨-, ⟨g, hgcs, rfl⟩, rfl⟩
  obtain ⟨f, hf⟩ := exists_solution d hc g hgcs
  refine ⟨⟨toL2 d f, mem_domain_freeLaplacian d f⟩, ?_⟩
  have hval : shiftMap (freeLaplacian d) c ⟨toL2 d f, mem_domain_freeLaplacian d f⟩
      = toL2 d (negLaplacianS d f + c • f) := by
    rw [shiftMap_apply, freeLaplacian_apply, _root_.map_add, _root_.map_smul]
  rw [hval, hf]
  show toL2 d (𝓕⁻ g) = 𝓕⁻ (toL2 d g)
  exact (SchwartzMap.toLp_fourierInv_eq g).symm

/-! ## Main theorem -/

/-- **The free Laplacian is essentially self-adjoint.**  The operator `-Δ` with domain the
Schwartz space `𝓢(ℝ^d, ℂ)` inside `L²(ℝ^d, ℂ)` is essentially self-adjoint; the proof goes
through the Fourier transform, which turns `-Δ` into multiplication by `4π²‖ξ‖²`. -/
theorem freeLaplacian_essentiallySelfAdjoint_of_fourier :
    EssentiallySelfAdjoint (freeLaplacian d) := by
  refine essentiallySelfAdjoint_of_dense_shift_ranges (dense_domain_freeLaplacian d)
    (freeLaplacian_isSymmetric d) (dense_shift_range d ?_) (dense_shift_range d ?_)
  · intro ξ h
    have him := congrArg Complex.im h
    simp only [symbol, Complex.add_im, Complex.ofReal_im, Complex.I_im, Complex.zero_im] at him
    norm_num at him
  · intro ξ h
    have him := congrArg Complex.im h
    simp only [symbol, Complex.add_im, Complex.ofReal_im, Complex.neg_im, Complex.I_im,
      Complex.zero_im] at him
    norm_num at him

end Brockian.Weyl.FreeLaplacian2

