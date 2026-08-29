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
# Free Laplacian Essentially Self Adjoint Via Plancherel
Category: Brockian (Open Discharge)
Target: Brockian.FreeLaplacianPlancherel.freeLaplacian_essentiallySelfAdjoint_via_plancherel
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header above is a plain block comment because Lean requires `import` to precede any
-- module docstring; the same header is repeated as a module docstring below.)

import Mathlib

/-!
# Free Laplacian Essentially Self Adjoint Via Plancherel
Category: Brockian (Open Discharge)
Target: Brockian.FreeLaplacianPlancherel.freeLaplacian_essentiallySelfAdjoint_via_plancherel
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory SchwartzMap Laplacian LineDeriv FourierTransform Real LinearPMap
open scoped ComplexConjugate

namespace Brockian.FreeLaplacianPlancherel

/-- Euclidean space `ℝ^d`, the configuration space of the free particle. -/
abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The Hilbert space `L²(ℝ^d, ℂ)`. -/
noncomputable abbrev Hs (d : ℕ) := Lp ℂ 2 (volume : Measure (Space d))

variable {d : ℕ}

/-- The symbol (Fourier multiplier) of `-Δ`, namely `4π²‖ξ‖²`. -/
noncomputable def symbol (ξ : Space d) : ℝ := 4 * π ^ 2 * ‖ξ‖ ^ 2

lemma symbol_nonneg (ξ : Space d) : 0 ≤ symbol ξ := by
  unfold symbol; positivity

lemma continuous_symbol : Continuous (symbol (d := d)) := by
  unfold symbol; fun_prop

/-! ## The Fourier transform of the Laplacian on Schwartz space -/

/-- The Fourier transform turns the Laplacian into multiplication by `-4π²‖ξ‖²`. -/
lemma fourier_laplacian_apply (f : 𝓢(Space d, ℂ)) (ξ : Space d) :
    𝓕 (Δ f) ξ = -(symbol ξ : ℝ) * 𝓕 f ξ := by
  set b := stdOrthonormalBasis ℝ (Space d) with hb
  rw [laplacian_eq_sum b f, fourier_sum]
  have key : ∀ i, 𝓕 (∂_{b i} (∂_{b i} f)) ξ = -(4 * π ^ 2 * (inner ℝ ξ (b i)) ^ 2 : ℝ) * 𝓕 f ξ := by
    intro i
    have h1 : Function.HasTemperateGrowth (fun x : Space d => (inner ℝ x (b i) : ℝ)) := by
      fun_prop
    rw [fourier_lineDerivOp_eq, fourier_lineDerivOp_eq]
    simp only [SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply h1, Complex.real_smul,
      smul_eq_mul]
    push_cast
    ring_nf
    simp [Complex.I_sq]
  simp only [SchwartzMap.sum_apply, key]
  rw [← Finset.sum_mul]
  congr 1
  have hsum : ∑ i, (inner ℝ ξ (b i) : ℝ) ^ 2 = ‖ξ‖ ^ 2 := OrthonormalBasis.sum_sq_inner_left b ξ
  calc ∑ i, (-(4 * π ^ 2 * (inner ℝ ξ (b i)) ^ 2 : ℝ) : ℂ)
      = ((∑ i, -(4 * π ^ 2 * (inner ℝ ξ (b i)) ^ 2) : ℝ) : ℂ) := by push_cast; ring_nf
    _ = ((-(4 * π ^ 2 * ‖ξ‖ ^ 2) : ℝ) : ℂ) := by
        congr 1
        rw [← hsum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    _ = -(symbol ξ : ℝ) := by rw [symbol]; push_cast; ring

/-- The Fourier transform turns `-Δ` into multiplication by the (real, nonnegative) symbol. -/
lemma fourier_freeLaplacian_apply (f : 𝓢(Space d, ℂ)) (ξ : Space d) :
    𝓕 (-Δ f) ξ = (symbol ξ : ℝ) * 𝓕 f ξ := by
  rw [FourierTransform.fourier_neg (Δ f), SchwartzMap.neg_apply, fourier_laplacian_apply]
  ring

/-! ## The free Laplacian as an unbounded operator on `L²` -/

/-- The canonical embedding of Schwartz space into `L²`. -/
noncomputable def toLpLM : 𝓢(Space d, ℂ) →ₗ[ℂ] Hs d :=
  (toLpCLM ℂ ℂ 2 (volume : Measure (Space d))).toLinearMap

lemma toLpLM_apply (f : 𝓢(Space d, ℂ)) :
    toLpLM f = f.toLp 2 (volume : Measure (Space d)) := rfl

lemma toLp_neg (f : 𝓢(Space d, ℂ)) :
    ((-Δ f).toLp 2 (volume : Measure (Space d)))
      = -((Δ f).toLp 2 (volume : Measure (Space d))) := by
  rw [← SchwartzMap.toLpCLM_apply (𝕜 := ℂ) (p := 2), ← SchwartzMap.toLpCLM_apply (𝕜 := ℂ) (p := 2),
    ← _root_.map_neg]

/-- `-Δ` as a linear map from Schwartz space into `L²`. -/
noncomputable def freeLaplacianLM : 𝓢(Space d, ℂ) →ₗ[ℂ] Hs d :=
  (toLpCLM ℂ ℂ 2 (volume : Measure (Space d))).toLinearMap ∘ₗ
    (-(laplacianCLM ℂ (Space d) 𝓢(Space d, ℂ))).toLinearMap

lemma freeLaplacianLM_apply (f : 𝓢(Space d, ℂ)) :
    freeLaplacianLM f = (-Δ f).toLp 2 (volume : Measure (Space d)) := by
  simp [freeLaplacianLM, SchwartzMap.laplacianCLM_eq, toLp_neg]

/-- Schwartz functions are determined by their class in `L²`. -/
lemma toLp_injective : Function.Injective (toLpLM (d := d)) := by
  intro f g h
  have hf := f.coeFn_toLp 2 (volume : Measure (Space d))
  have hg := g.coeFn_toLp 2 (volume : Measure (Space d))
  have h' : f.toLp 2 (volume : Measure (Space d)) = g.toLp 2 (volume : Measure (Space d)) := h
  have hae : (f : Space d → ℂ) =ᵐ[volume] (g : Space d → ℂ) := by
    filter_upwards [hf, hg] with x hx hx'
    rw [← hx, ← hx', h']
  exact DFunLike.ext' ((Continuous.ae_eq_iff_eq volume f.continuous g.continuous).mp hae)

/-- The free Laplacian `-Δ` as an unbounded operator on `L²(ℝ^d)` whose domain is the (image in
`L²` of the) Schwartz space. -/
noncomputable def freeLaplacianPMap (d : ℕ) : Hs d →ₗ.[ℂ] Hs d where
  domain := LinearMap.range (toLpLM (d := d))
  toFun := freeLaplacianLM ∘ₗ
    (LinearEquiv.ofInjective (toLpLM (d := d)) toLp_injective).symm.toLinearMap

lemma mem_domain (f : 𝓢(Space d, ℂ)) : toLpLM f ∈ (freeLaplacianPMap d).domain :=
  ⟨f, rfl⟩

lemma freeLaplacianPMap_apply (f : 𝓢(Space d, ℂ)) (hf : toLpLM f ∈ (freeLaplacianPMap d).domain) :
    (freeLaplacianPMap d) ⟨toLpLM f, hf⟩ = (-Δ f).toLp 2 (volume : Measure (Space d)) := by
  have hsymm : (LinearEquiv.ofInjective (toLpLM (d := d)) toLp_injective).symm
      ⟨toLpLM f, hf⟩ = f := by
    apply toLp_injective
    exact LinearEquiv.ofInjective_symm_apply _ _
  show freeLaplacianLM ((LinearEquiv.ofInjective (toLpLM (d := d)) toLp_injective).symm
      ⟨toLpLM f, hf⟩) = _
  rw [hsymm, freeLaplacianLM_apply]

lemma dense_domain : Dense ((freeLaplacianPMap d).domain : Set (Hs d)) := by
  have h := SchwartzMap.denseRange_toLpCLM (E := Space d) (F := ℂ) (p := 2)
    (ENNReal.ofNat_ne_top) (μ := (volume : Measure (Space d)))
  have hset : ((freeLaplacianPMap d).domain : Set (Hs d))
      = Set.range (toLpCLM ℝ ℂ 2 (volume : Measure (Space d))) := by
    ext x
    simp [freeLaplacianPMap, toLpLM, SchwartzMap.toLpCLM_apply]
  rw [hset]
  exact h

/-! ## Inner products as integrals -/

/-- The `L²` inner product against (the class of) a Schwartz function, as an integral. -/
lemma inner_toLp (u : Hs d) (f : 𝓢(Space d, ℂ)) :
    inner ℂ u (f.toLp 2 (volume : Measure (Space d))) = ∫ ξ, conj (u ξ) * f ξ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [f.coeFn_toLp 2 (volume : Measure (Space d))] with x hx
  rw [hx]
  simp only [RCLike.inner_apply]
  ring

/-- The `L²` inner product of two Schwartz functions, as an integral. -/
lemma inner_toLp_toLp (f g : 𝓢(Space d, ℂ)) :
    inner ℂ (f.toLp 2 (volume : Measure (Space d))) (g.toLp 2 (volume : Measure (Space d)))
      = ∫ ξ, conj (f ξ) * g ξ := by
  rw [inner_toLp]
  refine integral_congr_ae ?_
  filter_upwards [f.coeFn_toLp 2 (volume : Measure (Space d))] with x hx
  rw [hx]

/-! ## Symmetry of the free Laplacian, via Plancherel -/

/-- `-Δ` is symmetric on Schwartz space: this is Plancherel plus the fact that the symbol is
real-valued. -/
lemma inner_freeLaplacian_symm (f g : 𝓢(Space d, ℂ)) :
    inner ℂ ((-Δ f).toLp 2 (volume : Measure (Space d)))
        (g.toLp 2 (volume : Measure (Space d)))
      = inner ℂ (f.toLp 2 (volume : Measure (Space d)))
        ((-Δ g).toLp 2 (volume : Measure (Space d))) := by
  rw [← MeasureTheory.Lp.inner_fourier_eq ((-Δ f).toLp 2 (volume : Measure (Space d)))
        (g.toLp 2 (volume : Measure (Space d))),
    ← MeasureTheory.Lp.inner_fourier_eq (f.toLp 2 (volume : Measure (Space d)))
        ((-Δ g).toLp 2 (volume : Measure (Space d)))]
  simp only [SchwartzMap.toLp_fourier_eq]
  rw [inner_toLp_toLp, inner_toLp_toLp]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  dsimp only
  rw [fourier_freeLaplacian_apply, fourier_freeLaplacian_apply]
  simp only [map_mul, Complex.conj_ofReal]
  ring

lemma isFormalAdjoint_self : (freeLaplacianPMap d).IsFormalAdjoint (freeLaplacianPMap d) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  obtain ⟨f, rfl⟩ := hx
  obtain ⟨g, rfl⟩ := hy
  rw [freeLaplacianPMap_apply f, freeLaplacianPMap_apply g]
  exact inner_freeLaplacian_symm f g

lemma le_adjoint_self : freeLaplacianPMap d ≤ (freeLaplacianPMap d)† :=
  LinearPMap.IsFormalAdjoint.le_adjoint dense_domain isFormalAdjoint_self

lemma dense_adjoint_domain : Dense (((freeLaplacianPMap d)†).domain : Set (Hs d)) :=
  dense_domain.mono (fun _ hx => le_adjoint_self.1 hx)

/-! ## The Fourier description of the adjoint -/

lemma locallyIntegrable_symbol_mul (u : Hs d) :
    LocallyIntegrable (fun ξ => (symbol ξ : ℂ) * (u : Space d → ℂ) ξ) volume := by
  have hu : LocallyIntegrable (fun ξ => (u : Space d → ℂ) ξ) volume :=
    (Lp.memLp u).locallyIntegrable one_le_two
  have hc : Continuous (fun ξ : Space d => (symbol ξ : ℂ)) :=
    Complex.continuous_ofReal.comp continuous_symbol
  rw [MeasureTheory.locallyIntegrable_iff] at hu ⊢
  intro K hK
  exact IntegrableOn.continuousOn_mul hc.continuousOn (hu K hK) hK

/-- Key consequence of Plancherel: if `w` is a distributional value of `-Δ u`, then on the Fourier
side `w` is the multiplication of `u` by the symbol. -/
lemma fourier_of_formal (u w : Hs d)
    (h : ∀ f : 𝓢(Space d, ℂ), inner ℂ w (f.toLp 2 (volume : Measure (Space d)))
      = inner ℂ u ((-Δ f).toLp 2 (volume : Measure (Space d)))) :
    (fun ξ => (𝓕 w) ξ) =ᵐ[(volume : Measure (Space d))] fun ξ => (symbol ξ : ℂ) * (𝓕 u) ξ := by
  -- On the Fourier side, testing against `g` amounts to testing against `symbol * g`.
  have key : ∀ g : 𝓢(Space d, ℂ), ∫ ξ, conj ((𝓕 w) ξ) * g ξ
      = ∫ ξ, conj ((𝓕 u) ξ) * ((symbol ξ : ℂ) * g ξ) := by
    intro g
    set f : 𝓢(Space d, ℂ) := 𝓕⁻ g with hf
    have hfg : 𝓕 f = g := by rw [hf]; exact FourierTransform.fourier_fourierInv_eq g
    have e1 : inner ℂ (𝓕 w) (g.toLp 2 (volume : Measure (Space d)))
        = inner ℂ w (f.toLp 2 (volume : Measure (Space d))) := by
      rw [← hfg, ← SchwartzMap.toLp_fourier_eq, MeasureTheory.Lp.inner_fourier_eq]
    have e2 : inner ℂ u ((-Δ f).toLp 2 (volume : Measure (Space d)))
        = inner ℂ (𝓕 u) ((𝓕 (-Δ f)).toLp 2 (volume : Measure (Space d))) := by
      rw [← SchwartzMap.toLp_fourier_eq, MeasureTheory.Lp.inner_fourier_eq]
    have e3 := e1.trans ((h f).trans e2)
    rw [inner_toLp, inner_toLp] at e3
    rw [e3]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    dsimp only
    rw [fourier_freeLaplacian_apply, hfg]
  -- Now use that a locally integrable function is determined by its action on test functions.
  refine ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (𝓕 w)).locallyIntegrable one_le_two) (locallyIntegrable_symbol_mul (𝓕 u)) ?_
  intro φ hφ hφc
  have hcd := Complex.ofRealCLM.contDiff.comp hφ
  have hcs : HasCompactSupport (fun x : Space d => (φ x : ℂ)) :=
    hφc.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  set g : 𝓢(Space d, ℂ) := hcs.toSchwartzMap hcd with hg
  have hgval : ∀ x, g x = (φ x : ℂ) := fun _ => rfl
  have h1 := key g
  simp only [hgval] at h1
  have hconj := congrArg (starRingEnd ℂ) h1
  rw [← integral_conj, ← integral_conj] at hconj
  simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal] at hconj
  refine (integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)).trans
    (hconj.trans (integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)))
  · simp only [Complex.real_smul]; ring
  · simp only [Complex.real_smul]; ring

/-- Every element of the domain of the adjoint is described on the Fourier side by multiplication
with the symbol. -/
lemma fourier_adjoint_apply (u : ((freeLaplacianPMap d)†).domain) :
    (fun ξ => (𝓕 ((freeLaplacianPMap d)† u)) ξ)
      =ᵐ[(volume : Measure (Space d))] fun ξ => (symbol ξ : ℂ) * (𝓕 (u : Hs d)) ξ := by
  refine fourier_of_formal (u : Hs d) ((freeLaplacianPMap d)† u) fun f => ?_
  have := LinearPMap.adjoint_isFormalAdjoint (T := freeLaplacianPMap d) dense_domain u
    ⟨toLpLM f, mem_domain f⟩
  rw [freeLaplacianPMap_apply f] at this
  exact this

/-- The adjoint of the free Laplacian is symmetric.  This is the heart of essential
self-adjointness: on the Fourier side the operator is multiplication by the *real* symbol. -/
lemma adjoint_isFormalAdjoint_self :
    ((freeLaplacianPMap d)†).IsFormalAdjoint ((freeLaplacianPMap d)†) := by
  intro u v
  have hu := fourier_adjoint_apply u
  have hv := fourier_adjoint_apply v
  have h1 : inner ℂ ((freeLaplacianPMap d)† u) (v : Hs d)
      = inner ℂ (𝓕 ((freeLaplacianPMap d)† u)) (𝓕 (v : Hs d)) :=
    (MeasureTheory.Lp.inner_fourier_eq _ _).symm
  have h2 : inner ℂ ((u : Hs d)) ((freeLaplacianPMap d)† v)
      = inner ℂ (𝓕 (u : Hs d)) (𝓕 ((freeLaplacianPMap d)† v)) :=
    (MeasureTheory.Lp.inner_fourier_eq _ _).symm
  rw [h1, h2, MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hu, hv] with ξ hξu hξv
  simp only [RCLike.inner_apply] at *
  rw [hξu, hξv]
  simp only [map_mul, Complex.conj_ofReal]
  ring

/-- **The free Laplacian is essentially self-adjoint.**

`freeLaplacianPMap d` is the operator `-Δ` on `L²(ℝ^d)` with domain the Schwartz space.
Essential self-adjointness of a densely defined symmetric operator `T` is exactly
self-adjointness of its adjoint `T†` (equivalently `T†† = T†`, i.e. the closure `T†† = T̄` of `T`
is self-adjoint).  The proof goes through the Plancherel theorem: on the Fourier side `-Δ` is
multiplication by the real symbol `4π²‖ξ‖²`. -/
theorem freeLaplacian_essentiallySelfAdjoint_via_plancherel (d : ℕ) :
    IsSelfAdjoint ((freeLaplacianPMap d)†) := by
  rw [LinearPMap.isSelfAdjoint_def]
  refine le_antisymm ?_ ?_
  · -- `T†† ≤ T†`, since `T ≤ T†`.
    refine LinearPMap.IsFormalAdjoint.le_adjoint (T := freeLaplacianPMap d) dense_domain ?_
    intro x y
    have hx' : (x : Hs d) ∈ ((freeLaplacianPMap d)†).domain := le_adjoint_self.1 x.2
    have hxx : (freeLaplacianPMap d) x = (freeLaplacianPMap d)† ⟨(x : Hs d), hx'⟩ :=
      le_adjoint_self.2 rfl
    rw [hxx]
    exact (LinearPMap.adjoint_isFormalAdjoint (T := (freeLaplacianPMap d)†)
      dense_adjoint_domain).symm ⟨(x : Hs d), hx'⟩ y
  · -- `T† ≤ T††`, since `T†` is symmetric.
    exact LinearPMap.IsFormalAdjoint.le_adjoint dense_adjoint_domain adjoint_isFormalAdjoint_self

end Brockian.FreeLaplacianPlancherel

