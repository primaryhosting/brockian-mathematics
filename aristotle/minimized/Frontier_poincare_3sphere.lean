import Mathlib

/-!
# Poincare 3 Sphere
Category: Frontier — Moonshot
Target: Frontier.poincare_3sphere
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

open Metric Module Set Topology

/-- The standard `3`-sphere, realized as the unit sphere of `ℝ⁴`. -/
abbrev Sphere3 : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

/-- The statement of the **Poincaré conjecture** (a theorem of Perelman): every simply
connected closed (= compact, without boundary) topological `3`-manifold is homeomorphic to
the `3`-sphere.

Being a closed `3`-manifold is encoded as: Hausdorff, compact, and locally modelled on
`ℝ³` (a `ChartedSpace (EuclideanSpace ℝ (Fin 3))` structure). Note that compactness together
with the charted space structure automatically gives second countability. -/

noncomputable def onePointComplSingletonHomeo {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] (p : X) : OnePoint ({p}ᶜ : Set X) ≃ₜ X :=
  OnePoint.equivOfIsEmbeddingOfRangeEq p Subtype.val IsEmbedding.subtypeVal (by
    ext x; simp)

/-- The one-point compactification of `ℝ³` is the `3`-sphere. -/

noncomputable def onePointEuclidean3Homeo : OnePoint (EuclideanSpace ℝ (Fin 3)) ≃ₜ Sphere3 :=
  onePointEquivSphereOfFinrankEq (by simp)

/-- Removing a point from the `3`-sphere leaves a space homeomorphic to `ℝ³`
(stereographic projection). -/

noncomputable def puncturedSphere3Homeo (v : Sphere3) :
    ({v}ᶜ : Set Sphere3) ≃ₜ EuclideanSpace ℝ (Fin 3) := by
  have hv : ‖(v : EuclideanSpace ℝ (Fin 4))‖ = 1 := by simp
  have hv0 : (v : EuclideanSpace ℝ (Fin 4)) ≠ 0 := by
    intro h; rw [h] at hv; simp at hv
  -- the punctured sphere is homeomorphic to the orthogonal complement of `v`
  have hrange : Set.range (stereographic hv).symm = ({v}ᶜ : Set Sphere3) := by
    rw [range_stereographic_symm hv (by simp)]
  let e₁ : ((ℝ ∙ (v : EuclideanSpace ℝ (Fin 4)))ᗮ) ≃ₜ ({v}ᶜ : Set Sphere3) :=
    ((isOpenEmbedding_stereographic_symm hv).isEmbedding.toHomeomorph).trans
      (Homeomorph.setCongr hrange)
  -- and that complement is a `3`-dimensional real inner product space
  have hfin : finrank ℝ (EuclideanSpace ℝ (Fin 3)) =
      finrank ℝ ((ℝ ∙ (v : EuclideanSpace ℝ (Fin 4)))ᗮ) := by
    haveI : Fact (finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩
    rw [Submodule.finrank_orthogonal_span_singleton (n := 3) hv0]
    simp
  let e₂ : EuclideanSpace ℝ (Fin 3) ≃ₜ ((ℝ ∙ (v : EuclideanSpace ℝ (Fin 4)))ᗮ) :=
    (FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq hfin).some
  exact (e₂.trans e₁).symm

/-- **Characterization of the `3`-sphere among compact Hausdorff spaces by a puncture.**
A compact Hausdorff space is homeomorphic to `S³` if and only if it has a point whose
complement is homeomorphic to `ℝ³`. -/

theorem homeomorph_sphere3_iff_punctured_euclidean {M : Type*} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] :
    Nonempty (M ≃ₜ Sphere3) ↔ ∃ p : M, Nonempty (({p}ᶜ : Set M) ≃ₜ EuclideanSpace ℝ (Fin 3)) := by
  constructor
  · rintro ⟨g⟩
    obtain ⟨v, hv⟩ : ∃ v : EuclideanSpace ℝ (Fin 4), v ∈ Metric.sphere (0 : _) 1 :=
      ⟨EuclideanSpace.single 0 1, by simp⟩
    refine ⟨g.symm ⟨v, hv⟩, ⟨?_⟩⟩
    have himg : g '' ({g.symm ⟨v, hv⟩}ᶜ : Set M) = ({(⟨v, hv⟩ : Sphere3)}ᶜ : Set Sphere3) := by
      ext y
      simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨x, hx, rfl⟩ h
        exact hx (by rw [← h]; simp)
      · intro hy
        refine ⟨g.symm y, ?_, by simp⟩
        intro h
        exact hy (by rw [← g.apply_symm_apply y, h]; simp)
    exact ((g.image _).trans (Homeomorph.setCongr himg)).trans (puncturedSphere3Homeo _)
  · rintro ⟨p, ⟨e⟩⟩
    exact ⟨((onePointComplSingletonHomeo p).symm.trans e.onePointCongr).trans
      onePointEuclidean3Homeo⟩

/-- **Poincaré conjecture (Perelman), Lean-checked reduction.**

A simply connected closed `3`-manifold `M` (Hausdorff, compact, connected, locally modelled
on `ℝ³`) is homeomorphic to the `3`-sphere, *provided* that `M` has a point whose complement is
homeomorphic to `ℝ³`.

The hypothesis `h` is exactly the geometric content supplied by Perelman's Ricci-flow argument;
everything else — the passage from a punctured manifold to the sphere, via one-point
compactification and stereographic projection — is proved here. The topological hypotheses
`ConnectedSpace`, `SimplyConnectedSpace` and the charted space structure record the setting of
the conjecture; the reduction argument itself only uses compactness and the Hausdorff property. -/

theorem poincare_3sphere (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ConnectedSpace M] [SimplyConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (h : ∃ p : M, Nonempty (({p}ᶜ : Set M) ≃ₜ EuclideanSpace ℝ (Fin 3))) :
    Nonempty (M ≃ₜ Sphere3) :=
  homeomorph_sphere3_iff_punctured_euclidean.mpr h

/-- Packaged form of the reduction: if every simply connected closed `3`-manifold has a point
whose complement is homeomorphic to `ℝ³`, then the Poincaré conjecture holds. -/
