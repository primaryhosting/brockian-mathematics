/-
# Ratner
Category: Frontier Math
Target: Math2.ratner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Math2

/-! ## Ratner's orbit closure theorem, abelian (torus) case

Ratner's orbit closure theorem states that if `U = {u_t}` is a one-parameter unipotent
subgroup of a Lie group `G` and `Γ ≤ G` is a lattice, then for every `x ∈ G/Γ` the closure
of the orbit `{u_t · x}` is a homogeneous set `x · H` for some closed connected subgroup
`H ≤ G` containing `U`, and the orbit is equidistributed with respect to the (unique)
`H`-invariant probability measure on `x · H`.

Here we formalise this in the abelian setting, which is a genuine instance of the theorem:
`G = ℝⁿ` is a (unipotent, abelian) Lie group, `Γ = ℤⁿ` is a lattice, the homogeneous space is
the torus `𝕋ⁿ = ℝⁿ/ℤⁿ`, and every one-parameter subgroup `t ↦ t · v` of `ℝⁿ` is unipotent.

* `Math2.orbitClosure_eq_coset` is the orbit closure statement: the closure of the orbit of
  a one-parameter subgroup is a coset of a closed connected subgroup containing the acting
  subgroup.
* `Math2.dense_orbit_irrational_slope` is the classical instance on the two-torus: the linear
  flow of irrational slope has all orbits dense (so there the subgroup `H` is everything).
-/

section OrbitClosure

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]

/-- **Orbit closure theorem, abelian case.** For a continuous one-parameter subgroup
`f : ℝ →+ G` of a topological abelian group `G` and any point `x`, the closure of the orbit
`{x + f t : t ∈ ℝ}` is the coset `x + H` of a closed connected subgroup `H` of `G`
containing the one-parameter subgroup. -/
theorem orbitClosure_eq_coset (f : ℝ →+ G) (hf : Continuous f) (x : G) :
    ∃ H : AddSubgroup G, IsClosed (H : Set G) ∧ IsConnected (H : Set G) ∧
      Set.range f ⊆ (H : Set G) ∧
      closure (Set.range fun t : ℝ => x + f t) = (fun h => x + h) '' (H : Set G) := by
  refine ⟨(AddMonoidHom.range f).topologicalClosure, ?_, ?_, ?_, ?_⟩
  · exact AddSubgroup.isClosed_topologicalClosure _
  · rw [AddSubgroup.topologicalClosure_coe]
    have : (AddMonoidHom.range f : Set G) = Set.range f := by
      ext y; simp
    rw [this]
    exact (isConnected_range hf).closure
  · rw [AddSubgroup.topologicalClosure_coe]
    refine subset_trans ?_ subset_closure
    intro y hy
    obtain ⟨t, rfl⟩ := hy
    exact ⟨t, rfl⟩
  · rw [AddSubgroup.topologicalClosure_coe]
    have hrange : (AddMonoidHom.range f : Set G) = Set.range f := by
      ext y; simp
    rw [hrange]
    have himg : (Set.range fun t : ℝ => x + f t) = (fun h => x + h) '' Set.range f := by
      ext y
      constructor
      · rintro ⟨t, rfl⟩; exact ⟨f t, ⟨t, rfl⟩, rfl⟩
      · rintro ⟨z, ⟨t, rfl⟩, rfl⟩; exact ⟨t, rfl⟩
    rw [himg]
    exact ((Homeomorph.addLeft x).image_closure (Set.range f)).symm

end OrbitClosure

/-! ## The linear flow on the two-torus -/

/-- The two-dimensional torus `𝕋² = ℝ²/ℤ²`. -/
abbrev Torus2 : Type := AddCircle (1 : ℝ) × AddCircle (1 : ℝ)

/-- The one-parameter (unipotent) subgroup `t ↦ (t, α t)` of `ℝ²`, viewed inside `𝕋²`. -/
def linearFlow (α : ℝ) : ℝ →+ Torus2 :=
  AddMonoidHom.mk' (fun t => (((t : ℝ) : AddCircle (1 : ℝ)), ((α * t : ℝ) : AddCircle (1 : ℝ))))
    (by
      intro a b
      have h : α * (a + b) = α * a + α * b := by ring
      simp [h, QuotientAddGroup.mk_add])

theorem continuous_linearFlow (α : ℝ) : Continuous (linearFlow α) := by
  apply Continuous.prodMk
  · exact continuous_quotient_mk'.comp continuous_id
  · exact continuous_quotient_mk'.comp (continuous_const.mul continuous_id)

theorem linearFlow_apply (α t : ℝ) :
    linearFlow α t = (((t : ℝ) : AddCircle (1 : ℝ)), ((α * t : ℝ) : AddCircle (1 : ℝ))) := rfl

/-- Multiples of an irrational number are dense in the circle `ℝ/ℤ`. -/
theorem denseRange_zsmul_irrational {α : ℝ} (hα : Irrational α) :
    DenseRange (fun n : ℤ => n • ((α : ℝ) : AddCircle (1 : ℝ))) := by
  rw [AddCircle.denseRange_zsmul_coe_iff]
  simpa using hα

/-- Translating a dense subset of a topological additive group keeps it dense. -/
theorem dense_add_left {A : Type*} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    (c : A) {s : Set A} (hs : Dense s) : Dense ((fun z => c + z) '' s) := by
  intro z
  have hcont : Continuous fun z : A => c + z := continuous_const.add continuous_id
  refine image_closure_subset_closure_image hcont ⟨-c + z, ?_, by simp⟩
  rw [hs.closure_eq]; trivial

/-- **Density of the irrational linear flow on the two-torus.** This is the instance of
Ratner's orbit closure theorem where the orbit closure is all of the homogeneous space. -/
theorem dense_orbit_irrational_slope {α : ℝ} (hα : Irrational α) (x : Torus2) :
    Dense (Set.range fun t : ℝ => x + linearFlow α t) := by
  intro y
  obtain ⟨r, hr⟩ := QuotientAddGroup.mk_surjective (s := AddSubgroup.zmultiples (1 : ℝ))
    (y.1 - x.1)
  have hy1 : y.1 = x.1 + ((r : ℝ) : AddCircle (1 : ℝ)) := by rw [hr]; abel
  set c : AddCircle (1 : ℝ) := x.2 + ((α * r : ℝ) : AddCircle (1 : ℝ)) with hc
  -- the sub-orbit at times `r + n`, `n : ℤ`, lies in `{y.1} ×ˢ (c + ℤα)`
  have hsub : ({y.1} : Set (AddCircle (1 : ℝ))) ×ˢ
      (Set.range fun n : ℤ => c + n • ((α : ℝ) : AddCircle (1 : ℝ)))
        ⊆ Set.range fun t : ℝ => x + linearFlow α t := by
    rintro ⟨z₁, z₂⟩ ⟨hz₁, ⟨n, hn⟩⟩
    have hz₁' : z₁ = y.1 := hz₁
    have hn' : c + n • ((α : ℝ) : AddCircle (1 : ℝ)) = z₂ := hn
    refine ⟨r + (n : ℝ), ?_⟩
    have hint : (((n : ℤ) : ℝ) : AddCircle (1 : ℝ)) = 0 := by simp
    have h1 : x.1 + ((r + (n : ℝ) : ℝ) : AddCircle (1 : ℝ)) = z₁ := by
      rw [AddCircle.coe_add, hint, hz₁', hy1]
      abel
    have hmul : ((α * (n : ℝ) : ℝ) : AddCircle (1 : ℝ))
        = n • ((α : ℝ) : AddCircle (1 : ℝ)) := by
      rw [mul_comm, ← zsmul_eq_mul]
      exact QuotientAddGroup.mk_zsmul _ _ _
    have h2 : x.2 + ((α * (r + (n : ℝ)) : ℝ) : AddCircle (1 : ℝ)) = z₂ := by
      rw [show α * (r + (n : ℝ)) = α * r + α * (n : ℝ) by ring, AddCircle.coe_add, hmul,
        ← hn', hc]
      abel
    apply Prod.ext
    · simpa [linearFlow_apply] using h1
    · simpa [linearFlow_apply] using h2
  -- the sub-orbit is dense
  have hdense : Dense (Set.range fun n : ℤ => c + n • ((α : ℝ) : AddCircle (1 : ℝ))) := by
    have himg : (Set.range fun n : ℤ => c + n • ((α : ℝ) : AddCircle (1 : ℝ)))
        = (fun z => c + z) '' Set.range (fun n : ℤ => n • ((α : ℝ) : AddCircle (1 : ℝ))) := by
      ext z
      constructor
      · rintro ⟨n, rfl⟩; exact ⟨_, ⟨n, rfl⟩, rfl⟩
      · rintro ⟨w, ⟨n, rfl⟩, rfl⟩; exact ⟨n, rfl⟩
    rw [himg]
    exact dense_add_left c (denseRange_zsmul_irrational hα)
  have hmem : y ∈ closure (({y.1} : Set (AddCircle (1 : ℝ))) ×ˢ
      (Set.range fun n : ℤ => c + n • ((α : ℝ) : AddCircle (1 : ℝ)))) := by
    rw [closure_prod_eq, hdense.closure_eq]
    exact ⟨by simp, Set.mem_univ _⟩
  exact closure_mono hsub hmem

/-! ## Ratner's measure classification theorem, abelian (torus) case

Ratner's measure classification theorem states that any ergodic probability measure invariant
under a one-parameter unipotent subgroup is the homogeneous (algebraic) measure on a closed
orbit. In the torus case treated here, the irrational linear flow on `𝕋²` is *uniquely
ergodic*: the only invariant Borel probability measure is the Haar (Lebesgue) measure. -/

open MeasureTheory

instance instFactZeroLtOne : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩

instance instIsProbabilityMeasureVolumeAddCircle :
    IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) :=
  ⟨by simp [AddCircle.measure_univ]⟩

instance instIsAddHaarMeasureVolumeTorus2 : (volume : Measure Torus2).IsAddHaarMeasure := by
  rw [show (volume : Measure Torus2)
      = (volume : Measure (AddCircle (1 : ℝ))).prod (volume : Measure (AddCircle (1 : ℝ))) from
    Measure.volume_eq_prod _ _]
  infer_instance

/-- For a finite measure on the torus, the translation average of a continuous function
depends continuously on the translation parameter. -/
theorem continuous_integral_translate (μ : Measure Torus2) [IsFiniteMeasure μ] {f : Torus2 → ℝ}
    (hf : Continuous f) : Continuous fun g : Torus2 => ∫ x, f (g + x) ∂μ := by
  have hcs : HasCompactSupport f := HasCompactSupport.of_compactSpace f
  have hν : Continuous fun g : Torus2 => ∫ y, f (-y + g) ∂(μ.map fun z : Torus2 => -z) :=
    continuous_integral_apply_neg_add hf hcs
  have heq : (fun g : Torus2 => ∫ y, f (-y + g) ∂(μ.map fun z : Torus2 => -z))
      = fun g : Torus2 => ∫ x, f (g + x) ∂μ := by
    funext g
    have hae : AEMeasurable (fun z : Torus2 => -z) μ := measurable_neg.aemeasurable
    have hsm : AEStronglyMeasurable (fun y : Torus2 => f (-y + g))
        (μ.map fun z : Torus2 => -z) :=
      (hf.comp (continuous_neg.add continuous_const)).aestronglyMeasurable
    rw [integral_map hae hsm]
    simp [add_comm]
  rwa [heq] at hν

/-- A probability measure on `𝕋²` invariant under the irrational linear flow is invariant
under *all* translations, since the flow orbit is dense. -/
theorem isAddLeftInvariant_of_flow_invariant {α : ℝ} (hα : Irrational α) (μ : Measure Torus2)
    [IsProbabilityMeasure μ] (hinv : ∀ t : ℝ, μ.map (fun x => linearFlow α t + x) = μ) :
    μ.IsAddLeftInvariant := by
  have hdense : Dense (Set.range (linearFlow α)) := by
    simpa using dense_orbit_irrational_slope hα (0 : Torus2)
  constructor
  intro g
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  have hmap : ∀ h : Torus2, ∫ x, f x ∂(μ.map fun x => h + x) = ∫ x, f (h + x) ∂μ := by
    intro h
    exact integral_map (measurable_const_add h).aemeasurable f.continuous.aestronglyMeasurable
  rw [hmap g]
  have hcont : Continuous fun g : Torus2 => ∫ x, f (g + x) ∂μ :=
    continuous_integral_translate μ f.continuous
  have hS : IsClosed {g : Torus2 | ∫ x, f (g + x) ∂μ = ∫ x, f x ∂μ} :=
    isClosed_eq hcont continuous_const
  have hsub : Set.range (linearFlow α) ⊆ {g : Torus2 | ∫ x, f (g + x) ∂μ = ∫ x, f x ∂μ} := by
    rintro _ ⟨t, rfl⟩
    show ∫ x, f (linearFlow α t + x) ∂μ = ∫ x, f x ∂μ
    rw [← hmap (linearFlow α t), hinv t]
  have huniv : Set.univ ⊆ {g : Torus2 | ∫ x, f (g + x) ∂μ = ∫ x, f x ∂μ} := by
    rw [← hdense.closure_eq]
    exact hS.closure_subset_iff.mpr hsub
  exact huniv (Set.mem_univ g)

/-- **Unique ergodicity (measure classification) for the irrational linear flow on `𝕋²`.**
Every Borel probability measure invariant under the flow `t ↦ x + (t, α t)` with `α`
irrational is the Haar (Lebesgue) probability measure. -/
theorem measure_classification_irrational_slope {α : ℝ} (hα : Irrational α) (μ : Measure Torus2)
    [IsProbabilityMeasure μ] (hinv : ∀ t : ℝ, μ.map (fun x => linearFlow α t + x) = μ) :
    μ = volume := by
  haveI : μ.IsAddLeftInvariant := isAddLeftInvariant_of_flow_invariant hα μ hinv
  have h := Measure.isAddInvariant_eq_smul_of_compactSpace μ (volume : Measure Torus2)
  have hu : (1 : ENNReal) = (μ.addHaarScalarFactor (volume : Measure Torus2) : ENNReal) := by
    have := congrArg (fun ν : Measure Torus2 => ν Set.univ) h
    simpa [ENNReal.smul_def] using this
  rw [h, show μ.addHaarScalarFactor (volume : Measure Torus2) = 1 by
    exact_mod_cast hu.symm, one_smul]

/-- The Haar (Lebesgue) measure on `𝕋²` is indeed invariant under the linear flow, so the
classification above is not vacuous. -/
theorem volume_flow_invariant (α t : ℝ) :
    (volume : Measure Torus2).map (fun x => linearFlow α t + x) = volume :=
  map_add_left_eq_self volume (linearFlow α t)

/-- **Ratner's orbit closure theorem in the abelian (torus) setting.**

The first component is the orbit closure statement: for any continuous one-parameter subgroup
`f` of a topological abelian group `G` (e.g. a one-parameter unipotent subgroup acting on the
homogeneous space `ℝⁿ/ℤⁿ`) and any base point `x`, the orbit closure of `x` is the coset
`x + H` of a closed connected subgroup `H` containing the acting one-parameter subgroup.

The second component is the classical instance on the two-torus `𝕋² = ℝ²/ℤ²`: for the linear
flow `t ↦ (t, α t)` with `α` irrational, every orbit is dense, i.e. `H` is the whole group.

The third component is the corresponding measure classification (unique ergodicity) statement:
the only Borel probability measure on `𝕋²` invariant under such a flow is the Haar (Lebesgue)
measure, i.e. the algebraic measure on the (whole) orbit closure. -/
theorem ratner :
    (∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
        (f : ℝ →+ G), Continuous f → ∀ x : G,
        ∃ H : AddSubgroup G, IsClosed (H : Set G) ∧ IsConnected (H : Set G) ∧
          Set.range f ⊆ (H : Set G) ∧
          closure (Set.range fun t : ℝ => x + f t) = (fun h => x + h) '' (H : Set G)) ∧
    (∀ α : ℝ, Irrational α → ∀ x : Torus2,
        Dense (Set.range fun t : ℝ => x + linearFlow α t)) ∧
    (∀ α : ℝ, Irrational α → ∀ μ : MeasureTheory.Measure Torus2,
        MeasureTheory.IsProbabilityMeasure μ →
        (∀ t : ℝ, μ.map (fun x => linearFlow α t + x) = μ) →
        μ = MeasureTheory.volume) := by
  refine ⟨?_, ?_, ?_⟩
  · intro G _ _ _ f hf x
    exact orbitClosure_eq_coset f hf x
  · intro α hα x
    exact dense_orbit_irrational_slope hα x
  · intro α hα μ hμ hinv
    exact measure_classification_irrational_slope hα μ hinv

end Math2

