import Mathlib

/-!
# Ratner
Category: Frontier Math
Target: Math2.ratner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real Nat Classical Pointwise

open MeasureTheory Topology Filter Set

namespace Math2

noncomputable section

/-! ## Setting

We work with the homogeneous space `X = G / Γ` where `G = ℝ²` is an abelian Lie group and
`Γ = ℤ²` is a lattice in it, so that `X` is the two–dimensional torus `𝕋² = ℝ²/ℤ²`.
Since `G` is abelian, every one–parameter subgroup `t ↦ t • v` of `G` is unipotent
(the adjoint representation is trivial), so the flow it induces on `X` is a unipotent flow.

This is the classical abelian model case of Ratner's theorems, containing the linear flows on
the torus with irrational slope. -/

/-- The two-dimensional torus `ℝ²/ℤ²`, the homogeneous space `G/Γ` for `G = ℝ²`, `Γ = ℤ²`. -/
abbrev Torus : Type := AddCircle (1 : ℝ) × AddCircle (1 : ℝ)

/-- The projection `ℝ² → ℝ²/ℤ²`. -/
def proj : ℝ × ℝ →+ Torus :=
  (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))).prodMap
    (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)))

@[simp] lemma proj_apply (z : ℝ × ℝ) : proj z = ((z.1 : AddCircle (1:ℝ)), (z.2 : AddCircle (1:ℝ))) :=
  rfl

lemma continuous_proj : Continuous proj := by
  exact (continuous_quotient_mk'.comp continuous_fst).prodMk
    (continuous_quotient_mk'.comp continuous_snd)

/-- The one-parameter unipotent subgroup of `G = ℝ²` in direction `v`, projected to `X`.
Explicitly `unipotentFlow v t = t • v mod ℤ²`. -/
def unipotentFlow (v : ℝ × ℝ) : ℝ →+ Torus :=
  AddMonoidHom.mk' (fun t : ℝ => proj (t • v)) (by
    intro a b
    simp [add_smul])

@[simp] lemma unipotentFlow_apply (v : ℝ × ℝ) (t : ℝ) :
    unipotentFlow v t = proj (t • v) := rfl

lemma continuous_unipotentFlow (v : ℝ × ℝ) : Continuous (unipotentFlow v) :=
  continuous_proj.comp (continuous_id.smul continuous_const)

/-- The closed connected subgroup `H` of `X` produced by Ratner's theorem: the closure of the
image of the one-parameter unipotent subgroup. -/
def H (v : ℝ × ℝ) : AddSubgroup Torus := (unipotentFlow v).range.topologicalClosure

lemma coe_H (v : ℝ × ℝ) : (H v : Set Torus) = closure (Set.range (unipotentFlow v)) := by
  simp [H, AddSubgroup.topologicalClosure_coe, AddMonoidHom.coe_range]

lemma isClosed_H (v : ℝ × ℝ) : IsClosed (H v : Set Torus) :=
  AddSubgroup.isClosed_topologicalClosure _

lemma isConnected_H (v : ℝ × ℝ) : IsConnected (H v : Set Torus) := by
  rw [coe_H]
  exact (isConnected_range (continuous_unipotentFlow v)).closure

lemma flow_mem_H (v : ℝ × ℝ) (t : ℝ) : unipotentFlow v t ∈ H v := by
  rw [SetLike.mem_coe.symm, coe_H]
  exact subset_closure ⟨t, rfl⟩

/-! ## Orbit closures -/

/-- **Ratner orbit closure theorem** (abelian case): every orbit closure of the unipotent flow
is the coset `x + H` of the closed connected subgroup `H`. -/
lemma orbitClosure_eq (v : ℝ × ℝ) (x : Torus) :
    closure (Set.range fun t : ℝ => x + unipotentFlow v t)
      = (fun h => x + h) '' (H v : Set Torus) := by
  have hrange : (Set.range fun t : ℝ => x + unipotentFlow v t)
      = (fun h => x + h) '' (Set.range (unipotentFlow v)) := by
    ext y; constructor
    · rintro ⟨t, rfl⟩; exact ⟨unipotentFlow v t, ⟨t, rfl⟩, rfl⟩
    · rintro ⟨-, ⟨t, rfl⟩, rfl⟩; exact ⟨t, rfl⟩
  rw [hrange, coe_H]
  exact ((Homeomorph.addLeft x).image_closure _).symm

/-! ## Invariant measures -/

/-- The set of translations preserving a probability measure on the torus is closed. -/
lemma isClosed_translationStabilizer (μ : Measure Torus) [IsProbabilityMeasure μ] :
    IsClosed {g : Torus | Measure.map (· + g) μ = μ} := by
  have key : {g : Torus | Measure.map (· + g) μ = μ}
      = ⋂ f : BoundedContinuousFunction Torus ℝ,
          {g : Torus | (∫ x, f (x + g) ∂μ) = ∫ x, f x ∂μ} := by
    ext g
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    have hmeas : Measurable (fun x : Torus => x + g) := measurable_add_const g
    haveI : IsProbabilityMeasure (Measure.map (fun x : Torus => x + g) μ) :=
      Measure.isProbabilityMeasure_map hmeas.aemeasurable
    constructor
    · intro hg f
      have h1 : ∫ x, f x ∂(Measure.map (fun x : Torus => x + g) μ) = ∫ x, f x ∂μ := by rw [hg]
      rwa [integral_map hmeas.aemeasurable f.continuous.aestronglyMeasurable] at h1
    · intro hf
      refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
      rw [integral_map hmeas.aemeasurable f.continuous.aestronglyMeasurable]
      exact hf f
  rw [key]
  refine isClosed_iInter fun f => ?_
  have hcont : Continuous fun g : Torus => ∫ x, f (x + g) ∂μ :=
    continuous_of_dominated (bound := fun _ => ‖f‖)
      (fun g => (f.continuous.comp (continuous_add_right g)).aestronglyMeasurable)
      (fun g => Filter.Eventually.of_forall fun x => f.norm_coe_le_norm _)
      (integrable_const _)
      (Filter.Eventually.of_forall fun x =>
        f.continuous.comp (continuous_const.add continuous_id))
  exact isClosed_eq hcont continuous_const

/-- **Ratner measure classification** (abelian case): a probability measure invariant under the
unipotent flow is automatically invariant under the whole closed connected subgroup `H`, i.e. it
is homogeneous along `H`. -/
lemma invariant_iff (v : ℝ × ℝ) (μ : Measure Torus) (hμ : IsProbabilityMeasure μ) :
    (∀ t : ℝ, Measure.map (· + unipotentFlow v t) μ = μ) ↔
      (∀ h ∈ H v, Measure.map (· + h) μ = μ) := by
  haveI := hμ
  constructor
  · intro hinv h hh
    have hsub : (H v : Set Torus) ⊆ {g : Torus | Measure.map (· + g) μ = μ} := by
      rw [coe_H]
      exact (isClosed_translationStabilizer μ).closure_subset_iff.mpr
        (by rintro - ⟨t, rfl⟩; exact hinv t)
    exact hsub hh
  · intro hH t
    exact hH _ (flow_mem_H v t)

/-! ## The homogeneous measure on a closed orbit -/

instance instCompactSpaceH (v : ℝ × ℝ) : CompactSpace ↑(H v) :=
  isCompact_iff_compactSpace.mp (isClosed_H v).isCompact

/-- The Haar probability measure of the compact group `H v`. -/
def haarH (v : ℝ × ℝ) : Measure ↑(H v) := Measure.addHaarMeasure ⊤

instance instIsAddHaarMeasureHaarH (v : ℝ × ℝ) : (haarH v).IsAddHaarMeasure := by
  unfold haarH; infer_instance

instance instIsProbabilityMeasureHaarH (v : ℝ × ℝ) : IsProbabilityMeasure (haarH v) :=
  ⟨by
    rw [haarH, show (Set.univ : Set ↑(H v))
        = ((⊤ : TopologicalSpace.PositiveCompacts ↑(H v)) : Set ↑(H v)) from rfl,
      Measure.addHaarMeasure_self]⟩

lemma measurable_cosetMap (v : ℝ × ℝ) (x : Torus) :
    Measurable (fun h : ↑(H v) => x + (h : Torus)) :=
  (continuous_const.add continuous_subtype_val).measurable

lemma isClosed_coset (v : ℝ × ℝ) (x : Torus) :
    IsClosed ((fun h => x + h) '' (H v : Set Torus)) :=
  (Homeomorph.addLeft x).isClosedMap _ (isClosed_H v)

/-- The homogeneous probability measure carried by the closed orbit `x + H v`. -/
def homogeneousMeasure (v : ℝ × ℝ) (x : Torus) : Measure Torus :=
  Measure.map (fun h : ↑(H v) => x + (h : Torus)) (haarH v)

instance instIsProbabilityMeasureHomogeneous (v : ℝ × ℝ) (x : Torus) :
    IsProbabilityMeasure (homogeneousMeasure v x) :=
  Measure.isProbabilityMeasure_map (measurable_cosetMap v x).aemeasurable

lemma integral_homogeneousMeasure (v : ℝ × ℝ) (x : Torus)
    (f : BoundedContinuousFunction Torus ℝ) :
    ∫ y, f y ∂(homogeneousMeasure v x) = ∫ h : ↑(H v), f (x + (h : Torus)) ∂(haarH v) := by
  rw [homogeneousMeasure, integral_map (measurable_cosetMap v x).aemeasurable
    f.continuous.aestronglyMeasurable]

lemma homogeneousMeasure_coset (v : ℝ × ℝ) (x : Torus) :
    homogeneousMeasure v x ((fun h => x + h) '' (H v : Set Torus)) = 1 := by
  rw [homogeneousMeasure, Measure.map_apply (measurable_cosetMap v x)
    (isClosed_coset v x).measurableSet]
  have : (fun h : ↑(H v) => x + (h : Torus)) ⁻¹' ((fun h => x + h) '' (H v : Set Torus))
      = Set.univ := by
    ext h
    simp only [Set.mem_preimage, Set.mem_univ, iff_true]
    exact ⟨(h : Torus), h.2, rfl⟩
  rw [this, measure_univ]

lemma homogeneousMeasure_invariant (v : ℝ × ℝ) (x : Torus) {g : Torus} (hg : g ∈ H v) :
    Measure.map (· + g) (homogeneousMeasure v x) = homogeneousMeasure v x := by
  rw [homogeneousMeasure, Measure.map_map (measurable_add_const g) (measurable_cosetMap v x)]
  have hcomp : ((fun y : Torus => y + g) ∘ fun h : ↑(H v) => x + (h : Torus))
      = (fun h : ↑(H v) => x + (h : Torus)) ∘ (fun h : ↑(H v) => h + ⟨g, hg⟩) := by
    funext h
    simp [add_assoc]
  rw [hcomp, ← Measure.map_map (measurable_cosetMap v x) (measurable_add_const _),
    map_add_right_eq_self (haarH v) (⟨g, hg⟩ : ↑(H v))]

/-- **Uniqueness of the invariant measure on a closed orbit**: an invariant probability measure
giving full mass to the closed orbit `x + H v` is the homogeneous measure of that orbit. -/
lemma eq_homogeneousMeasure_of_invariant (v : ℝ × ℝ) (x : Torus) (μ : Measure Torus)
    [IsProbabilityMeasure μ] (hinv : ∀ h ∈ H v, Measure.map (· + h) μ = μ)
    (hsupp : μ ((fun h => x + h) '' (H v : Set Torus)) = 1) :
    μ = homogeneousMeasure v x := by
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  set F : Torus → ℝ := fun y => ∫ h : ↑(H v), f (y + (h : Torus)) ∂(haarH v) with hFdef
  have hint : Integrable
      (Function.uncurry fun (y : Torus) (h : ↑(H v)) => f (y + (h : Torus)))
      (μ.prod (haarH v)) := by
    refine Integrable.mono' (integrable_const ‖f‖) ?_
      (Filter.Eventually.of_forall fun z => f.norm_coe_le_norm _)
    exact (f.continuous.comp
      (continuous_fst.add (continuous_subtype_val.comp continuous_snd))).aestronglyMeasurable
  -- averaging the invariance of `μ` over `H`
  have hinner : ∀ h : ↑(H v), (∫ y, f (y + (h : Torus)) ∂μ) = ∫ y, f y ∂μ := by
    intro h
    have hmeas : Measurable (fun y : Torus => y + (h : Torus)) := measurable_add_const _
    have h1 := hinv (h : Torus) h.2
    have h2 : ∫ y, f y ∂(Measure.map (fun y : Torus => y + (h : Torus)) μ) = ∫ y, f y ∂μ := by
      rw [h1]
    rwa [integral_map hmeas.aemeasurable f.continuous.aestronglyMeasurable] at h2
  have hswap : (∫ y, F y ∂μ) = ∫ y, f y ∂μ := by
    rw [hFdef]
    rw [integral_integral_swap hint]
    simp only [hinner]
    rw [integral_const, measure_univ, ENNReal.toReal_one, one_smul]
  -- `F` is constant along the coset `x + H v`
  have hcoset : ∀ y ∈ (fun h => x + h) '' (H v : Set Torus), F y = F x := by
    rintro - ⟨h₀, hh₀, rfl⟩
    have := integral_add_left_eq_self (μ := haarH v)
      (fun h : ↑(H v) => f (x + (h : Torus))) (⟨h₀, hh₀⟩ : ↑(H v))
    simpa [hFdef, add_assoc] using this
  have hae : F =ᵐ[μ] fun _ => F x := by
    have hnull : μ (((fun h => x + h) '' (H v : Set Torus))ᶜ) = 0 := by
      rw [measure_compl (isClosed_coset v x).measurableSet (measure_ne_top μ _), hsupp,
        measure_univ, tsub_self]
    filter_upwards [measure_zero_iff_ae_notMem.mp hnull] with y hy
    exact hcoset y (by simpa using hy)
  have hFint : (∫ y, F y ∂μ) = F x := by
    rw [integral_congr_ae hae, integral_const, measure_univ, ENNReal.toReal_one, one_smul]
  rw [← hswap, hFint, integral_homogeneousMeasure]

/-! ## The main statement -/

/-- **Ratner's theorems for unipotent flows**, in the abelian model case
`G = ℝ²`, `Γ = ℤ²`, `X = G/Γ = 𝕋²`, with the unipotent one-parameter subgroup
`u_t = t • v`.

There is a closed connected subgroup `H ≤ X` containing the whole orbit of the identity under
the flow such that:

* (orbit closure theorem) every orbit closure `cl {u_t · x}` is the homogeneous coset `x + H`;
* (measure classification) a Borel probability measure on `X` is invariant under the unipotent
  flow if and only if it is invariant under the (larger) group `H`, i.e. every invariant measure
  is homogeneous along `H`.
-/
theorem ratner (v : ℝ × ℝ) :
    (IsClosed (H v : Set Torus) ∧ IsConnected (H v : Set Torus) ∧
        ∀ t : ℝ, unipotentFlow v t ∈ H v) ∧
    (∀ x : Torus, closure (Set.range fun t : ℝ => x + unipotentFlow v t)
        = (fun h => x + h) '' (H v : Set Torus)) ∧
    (∀ μ : Measure Torus, IsProbabilityMeasure μ →
      ((∀ t : ℝ, Measure.map (· + unipotentFlow v t) μ = μ) ↔
        (∀ h ∈ H v, Measure.map (· + h) μ = μ))) :=
  ⟨⟨isClosed_H v, isConnected_H v, flow_mem_H v⟩, orbitClosure_eq v, invariant_iff v⟩

/-! ## The irrational linear flow on the torus -/

lemma flow_eq (a t : ℝ) :
    unipotentFlow (1, a) t = ((t : AddCircle (1:ℝ)), ((t * a : ℝ) : AddCircle (1:ℝ))) := by
  simp [Prod.smul_mk, smul_eq_mul]

lemma coe_int_zero (n : ℤ) : ((n : ℝ) : AddCircle (1:ℝ)) = 0 := by
  rw [AddCircle.coe_eq_zero_iff]
  exact ⟨n, by simp⟩

/-- For an irrational slope, `H` contains the whole vertical circle through the origin: this is
the density of the irrational rotation orbit `{nα mod 1}`. -/
lemma zero_mem_fiber {a : ℝ} (ha : Irrational a) (w : AddCircle (1:ℝ)) :
    ((0 : AddCircle (1:ℝ)), w) ∈ H (1, a) := by
  have hdense : DenseRange (fun n : ℤ => n • ((a : AddCircle (1:ℝ)))) :=
    AddCircle.denseRange_zsmul_coe_iff.mpr (by simpa using ha)
  have hphi : Continuous (fun u : AddCircle (1:ℝ) => ((0 : AddCircle (1:ℝ)), u)) :=
    continuous_const.prodMk continuous_id
  have hsub : (fun u : AddCircle (1:ℝ) => ((0 : AddCircle (1:ℝ)), u)) ''
      (Set.range (fun n : ℤ => n • ((a : AddCircle (1:ℝ))))) ⊆ (H (1, a) : Set Torus) := by
    rintro - ⟨-, ⟨n, rfl⟩, rfl⟩
    show ((0 : AddCircle (1:ℝ)), n • ((a : AddCircle (1:ℝ)))) ∈ (H (1, a) : Set Torus)
    have h1 : ((0 : AddCircle (1:ℝ)), n • ((a : AddCircle (1:ℝ))))
        = unipotentFlow (1, a) (n : ℝ) := by
      rw [flow_eq, coe_int_zero n, ← zsmul_eq_mul, QuotientAddGroup.mk_zsmul]
    rw [h1]
    exact flow_mem_H _ _
  have hmem : ((0 : AddCircle (1:ℝ)), w) ∈ closure ((fun u : AddCircle (1:ℝ) =>
      ((0 : AddCircle (1:ℝ)), u)) '' (Set.range (fun n : ℤ => n • ((a : AddCircle (1:ℝ)))))) := by
    apply image_closure_subset_closure_image hphi
    exact ⟨w, hdense w, rfl⟩
  have hcl := closure_mono hsub hmem
  rwa [(isClosed_H (1, a)).closure_eq] at hcl

/-- For an irrational slope `α`, the group `H` attached to the direction `(1, α)` is everything. -/
lemma H_eq_top_of_irrational {a : ℝ} (ha : Irrational a) : H (1, a) = ⊤ := by
  rw [AddSubgroup.eq_top_iff']
  rintro ⟨y1, y2⟩
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective (α := ℝ) y1
  have h1 : ((t : AddCircle (1:ℝ)), y2)
      = unipotentFlow (1, a) t + ((0 : AddCircle (1:ℝ)), y2 - ((t * a : ℝ) : AddCircle (1:ℝ))) := by
    rw [flow_eq]
    simp
  rw [h1]
  exact AddSubgroup.add_mem _ (flow_mem_H _ _) (zero_mem_fiber ha _)

/-- **Density of orbits**: for an irrational slope, every orbit of the linear flow on `𝕋²` is
dense. -/
theorem ratner_dense_orbit {a : ℝ} (ha : Irrational a) (x : Torus) :
    closure (Set.range fun t : ℝ => x + unipotentFlow (1, a) t) = Set.univ := by
  rw [orbitClosure_eq, H_eq_top_of_irrational ha]
  ext y
  simp only [AddSubgroup.coe_top, image_univ, mem_range, mem_univ, iff_true]
  exact ⟨y - x, by abel⟩

/-- **Unique ergodicity**: for an irrational slope, the only Borel probability measure on `𝕋²`
invariant under the linear flow is the Haar (Lebesgue) measure. -/
theorem ratner_unique_ergodicity {a : ℝ} (ha : Irrational a) (μ : Measure Torus)
    (hμ : IsProbabilityMeasure μ)
    (hinv : ∀ t : ℝ, Measure.map (· + unipotentFlow (1, a) t) μ = μ) :
    μ = (volume : Measure Torus) := by
  haveI := hμ
  have hall : ∀ g : Torus, Measure.map (· + g) μ = μ := fun g =>
    (invariant_iff (1, a) μ hμ).mp hinv g (by rw [H_eq_top_of_irrational ha]; trivial)
  haveI : μ.IsAddLeftInvariant := by
    constructor
    intro g
    have hfun : (fun x : Torus => g + x) = (fun x : Torus => x + g) := funext fun x => add_comm g x
    rw [hfun]
    exact hall g
  haveI : (volume : Measure Torus).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have hvol : (volume : Measure Torus) Set.univ = 1 := by
    rw [Measure.volume_eq_prod, ← Set.univ_prod_univ, Measure.prod_prod, AddCircle.measure_univ]
    simp
  have h := Measure.isAddLeftInvariant_eq_smul μ (volume : Measure Torus)
  have huniv := congrArg (fun ν : Measure Torus => ν Set.univ) h
  simp only [Measure.smul_apply, hvol, measure_univ, ENNReal.smul_def, smul_eq_mul,
    mul_one] at huniv
  have hc : μ.addHaarScalarFactor (volume : Measure Torus) = 1 := by exact_mod_cast huniv.symm
  rw [h, hc, one_smul]

end

end Math2

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

