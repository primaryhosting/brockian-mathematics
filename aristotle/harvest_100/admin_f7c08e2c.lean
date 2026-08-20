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

-- NOTE: Lean 4 requires `import` commands to come first in a file, so the required header
-- comment appears immediately after the import below.
import Mathlib

/-!
# Poincare 3 Sphere
Category: Frontier — Moonshot
Target: Frontier.poincare_3sphere
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Contents

The statement "every simply-connected closed 3-manifold is homeomorphic to `S³`" is Perelman's
theorem; nothing in Mathlib proves it. The closest thing Mathlib contains is the *statement*,
recorded as a `proof_wanted` in `Mathlib/Geometry/Manifold/PoincareConjecture.lean`:

```
/-- The 3-dimensional topological Poincaré conjecture (proven by Perelman) -/
proof_wanted SimplyConnectedSpace.nonempty_homeomorph_sphere_three
    [T2Space M] [ChartedSpace ℝ³ M] [SimplyConnectedSpace M] [CompactSpace M] :
    Nonempty (M ≃ₜ 𝕊³)
```

Since `proof_wanted` produces no declaration, there is no lemma to close the goal with. What is
proved here is therefore the formalized statement together with the base case and two
Lean-checked reductions, all packaged in `Frontier.poincare_3sphere`:

* **base case**: the `3`-sphere is itself a closed `3`-manifold, so the class of spaces the
  conjecture speaks about is nonempty and the target of the conclusion is in it;
* **reduction 1**: the conjecture is equivalent to its restriction to spaces additionally assumed
  nonempty, connected and locally path connected (these regularity hypotheses are free);
* **reduction 2**: the conjecture, in the "closed 3-manifold" formulation used here, is
  equivalent to Mathlib's `proof_wanted` formulation
  `SimplyConnectedSpace.nonempty_homeomorph_sphere_three` (quantified over all `M`).
-/

open Metric Set Topology TopologicalSpace

namespace Frontier

/-- The unit `3`-sphere, realized as the unit sphere of `ℝ⁴` with its subspace topology. -/
abbrev Sphere3 : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

/-- `M` is a *closed topological `3`-manifold*: a compact, Hausdorff, second countable space in
which every point has an open neighbourhood homeomorphic to `ℝ³` (in particular `M` has no
boundary). -/
structure IsClosed3Manifold (M : Type u) [TopologicalSpace M] : Prop where
  compactSpace : CompactSpace M
  t2Space : T2Space M
  secondCountable : SecondCountableTopology M
  locallyEuclidean : ∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
    Nonempty (U ≃ₜ EuclideanSpace ℝ (Fin 3))

/-- The Poincaré conjecture in dimension three (a theorem of Perelman): every simply connected
closed `3`-manifold is homeomorphic to the `3`-sphere. -/
def PoincareConjecture3 : Prop :=
  ∀ (M : Type) [TopologicalSpace M], IsClosed3Manifold M → SimplyConnectedSpace M →
    Nonempty (M ≃ₜ Sphere3)

/-- The `3`-dimensional topological Poincaré conjecture exactly as stated (as a `proof_wanted`)
in `Mathlib/Geometry/Manifold/PoincareConjecture.lean`, universally quantified over `M`. -/
def MathlibPoincareConjecture3 : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [SimplyConnectedSpace M] [CompactSpace M],
    Nonempty (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (3 + 1))) 1)

/-! ### Basic topology of closed `3`-manifolds -/

/-- Every closed `3`-manifold is locally path connected (being locally homeomorphic to `ℝ³`). -/
theorem IsClosed3Manifold.locPathConnectedSpace {M : Type u} [TopologicalSpace M]
    (hM : IsClosed3Manifold M) : LocPathConnectedSpace M := by
  rw [locPathConnectedSpace_iff_pathComponentIn_mem_nhds]
  intro x u hu hxu
  obtain ⟨U, hUopen, hxU, ⟨h⟩⟩ := hM.locallyEuclidean x
  haveI : LocPathConnectedSpace U := h.isOpenEmbedding.locPathConnectedSpace
  set x' : U := ⟨x, hxU⟩
  have hv : IsOpen ((Subtype.val : U → M) ⁻¹' u) := hu.preimage continuous_subtype_val
  have hx'v : x' ∈ (Subtype.val : U → M) ⁻¹' u := hxu
  set C : Set M := (Subtype.val : U → M) '' pathComponentIn ((Subtype.val : U → M) ⁻¹' u) x'
  have hopen : IsOpen C :=
    hUopen.isOpenEmbedding_subtypeVal.isOpenMap _ (hv.pathComponentIn _)
  have hpc : IsPathConnected C :=
    (isPathConnected_pathComponentIn hx'v).image continuous_subtype_val
  have hmem : x ∈ C := ⟨x', mem_pathComponentIn_self hx'v, rfl⟩
  have hsub : C ⊆ u := by
    rintro _ ⟨y, hy, rfl⟩
    have h' : y ∈ (Subtype.val : U → M) ⁻¹' u := pathComponentIn_subset hy
    exact h'
  exact Filter.mem_of_superset (hopen.mem_nhds hmem) (hpc.subset_pathComponentIn hmem hsub)

/-- Around every point of a closed `3`-manifold there is a chart onto `ℝ³`. -/
theorem IsClosed3Manifold.exists_chartAt {M : Type u} [TopologicalSpace M]
    (hM : IsClosed3Manifold M) (x : M) :
    ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)), x ∈ e.source := by
  obtain ⟨U, hUopen, hxU, ⟨h⟩⟩ := hM.locallyEuclidean x
  haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
  refine ⟨(hUopen.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph).symm.transHomeomorph h, ?_⟩
  simpa [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target] using hxU

/-- A closed `3`-manifold is a charted space modelled on `ℝ³`, i.e. it satisfies the hypothesis
`[ChartedSpace ℝ³ M]` used in Mathlib's statement of the conjecture. -/
noncomputable def IsClosed3Manifold.chartedSpace {M : Type u} [TopologicalSpace M]
    (hM : IsClosed3Manifold M) : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M where
  atlas := Set.range fun x : M => (hM.exists_chartAt x).choose
  chartAt x := (hM.exists_chartAt x).choose
  mem_chart_source x := (hM.exists_chartAt x).choose_spec
  chart_mem_atlas x := ⟨x, rfl⟩

/-- In a charted space modelled on `ℝ³`, every point has an open neighbourhood homeomorphic to
all of `ℝ³` (shrink a chart to a ball and use that a ball is homeomorphic to the whole space). -/
theorem exists_open_homeomorph_euclidean_of_chartedSpace {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] (x : M) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ Nonempty (U ≃ₜ EuclideanSpace ℝ (Fin 3)) := by
  set e := chartAt (EuclideanSpace ℝ (Fin 3)) x
  have hx : x ∈ e.source := mem_chart_source _ x
  have hc : e x ∈ e.target := e.map_source hx
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp e.open_target _ hc
  have hsub : ball (e x) r ⊆ e.symm.source := by rw [e.symm_source]; exact hball
  refine ⟨e.symm '' (ball (e x) r), e.symm.isOpen_image_of_subset_source Metric.isOpen_ball hsub,
    ⟨e x, Metric.mem_ball_self hr, e.left_inv hx⟩, ?_⟩
  have hball' : (ball (e x) r : Set (EuclideanSpace ℝ (Fin 3))) ≃ₜ (e.symm '' (ball (e x) r)) :=
    e.symm.homeomorphOfImageSubsetSource hsub rfl
  have hEuclid : EuclideanSpace ℝ (Fin 3) ≃ₜ (ball (e x) r : Set (EuclideanSpace ℝ (Fin 3))) :=
    ((Homeomorph.Set.univ (EuclideanSpace ℝ (Fin 3))).symm.trans
      ((Homeomorph.setCongr (OpenPartialHomeomorph.univBall_source (e x) r).symm).trans
        ((OpenPartialHomeomorph.univBall (e x) r).toHomeomorphSourceTarget))).trans
      (Homeomorph.setCongr (OpenPartialHomeomorph.univBall_target (e x) hr))
  exact ⟨(hEuclid.trans hball').symm⟩

/-- A compact space that is locally homeomorphic to `ℝ³` is second countable. -/
theorem secondCountable_of_compact_locallyEuclidean {M : Type} [TopologicalSpace M]
    [CompactSpace M] (hloc : ∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      Nonempty (U ≃ₜ EuclideanSpace ℝ (Fin 3))) : SecondCountableTopology M := by
  choose U hUopen hxU hhomeo using hloc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hUopen fun x _ => mem_iUnion.2 ⟨x, hxU x⟩
  haveI : ∀ i : (t : Set M), SecondCountableTopology (U i) :=
    fun i => (hhomeo i).some.secondCountableTopology
  refine secondCountableTopology_of_countable_cover (U := fun i : (t : Set M) => U i)
    (fun i => hUopen i) (eq_univ_iff_forall.2 fun x => ?_)
  have hx := ht (mem_univ x)
  simp only [mem_iUnion, exists_prop] at hx ⊢
  obtain ⟨i, hi, hxi⟩ := hx
  exact ⟨⟨i, hi⟩, hxi⟩

/-- A compact Hausdorff charted space modelled on `ℝ³` is a closed `3`-manifold. -/
theorem isClosed3Manifold_of_chartedSpace {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [CompactSpace M] : IsClosed3Manifold M where
  compactSpace := inferInstance
  t2Space := inferInstance
  secondCountable :=
    secondCountable_of_compact_locallyEuclidean exists_open_homeomorph_euclidean_of_chartedSpace
  locallyEuclidean := exists_open_homeomorph_euclidean_of_chartedSpace

/-! ### The `3`-sphere is a closed `3`-manifold -/

/-- The `3`-sphere is compact. -/
theorem sphere3_compactSpace : CompactSpace Sphere3 :=
  isCompact_iff_compactSpace.mp (isCompact_sphere _ _)

/-- Every point of the `3`-sphere has an open neighbourhood homeomorphic to `ℝ³`
(stereographic projection from the antipodal point). -/
theorem sphere3_locallyEuclidean (x : Sphere3) : ∃ U : Set Sphere3, IsOpen U ∧ x ∈ U ∧
    Nonempty (U ≃ₜ EuclideanSpace ℝ (Fin 3)) := by
  haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩
  set e := stereographic' 3 (-x) with he
  refine ⟨e.source, e.open_source, ?_, ?_⟩
  · rw [he, stereographic'_source]
    simpa using ne_neg_of_mem_unit_sphere ℝ x
  · exact ⟨e.toHomeomorphSourceTarget.trans
      ((Homeomorph.setCongr (stereographic'_target (n := 3) (-x))).trans (Homeomorph.Set.univ _))⟩

/-- **Base case.** The `3`-sphere really is a closed `3`-manifold, so the Poincaré conjecture is
a statement about a nonempty class of spaces whose conclusion is attained. -/
theorem sphere3_isClosed3Manifold : IsClosed3Manifold Sphere3 where
  compactSpace := sphere3_compactSpace
  t2Space := inferInstance
  secondCountable := inferInstance
  locallyEuclidean := sphere3_locallyEuclidean

/-! ### The target statement -/

/-- **Poincaré conjecture in dimension 3 (Perelman): statement, base case, and reductions.**

Mathlib contains no proof of Perelman's theorem — the only trace of it is the `proof_wanted`
`SimplyConnectedSpace.nonempty_homeomorph_sphere_three` in
`Mathlib/Geometry/Manifold/PoincareConjecture.lean`, which declares no term, so no `exact?`/
`apply?` can close the goal. What is proved here is:

1. the base case: the `3`-sphere `Sphere3` is a closed `3`-manifold;
2. a reduction: the conjecture `PoincareConjecture3` is equivalent to its restriction to spaces
   additionally assumed nonempty, connected and locally path connected;
3. a reduction: `PoincareConjecture3` is equivalent to Mathlib's own formulation of the
   conjecture, `MathlibPoincareConjecture3` (compact Hausdorff charted spaces modelled on `ℝ³`).
-/
theorem poincare_3sphere :
    IsClosed3Manifold Sphere3 ∧
      (PoincareConjecture3 ↔
        ∀ (M : Type) [TopologicalSpace M] [Nonempty M] [ConnectedSpace M]
          [LocPathConnectedSpace M],
          IsClosed3Manifold M → SimplyConnectedSpace M → Nonempty (M ≃ₜ Sphere3)) ∧
      (PoincareConjecture3 ↔ MathlibPoincareConjecture3) := by
  refine ⟨sphere3_isClosed3Manifold, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro h M _ _ _ _ hM hsc
    exact h M hM hsc
  · intro h M _ hM hsc
    have hpc : PathConnectedSpace M := inferInstance
    have : Nonempty M := hpc.nonempty
    have : ConnectedSpace M := inferInstance
    have := hM.locPathConnectedSpace
    exact h M hM hsc
  · intro h M _ _ _ _ _
    exact h M isClosed3Manifold_of_chartedSpace inferInstance
  · intro h M _ hM hsc
    letI := hM.t2Space
    letI := hM.compactSpace
    letI := hM.chartedSpace
    exact h M

end Frontier

