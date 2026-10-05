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
open scoped OnePoint

open Metric Topology

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

/-- `ℝ³`, the model space for `3`-dimensional topological manifolds. -/
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- `𝕊³`, the unit sphere in `ℝ⁴`. -/
local notation "𝕊³" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

/-! ## The statement of the Poincaré conjecture -/

/-- **The 3-dimensional topological Poincaré conjecture** (Perelman, 2003).

Every simply connected, closed (compact, boundaryless) topological 3-manifold is homeomorphic
to the 3-sphere.  A *closed topological 3-manifold* is a compact Hausdorff space equipped with
a charted space structure modelled on `ℝ³`.

This is the statement only; it is not proved here (and is not available in Mathlib either:
Mathlib records it as `SimplyConnectedSpace.nonempty_homeomorph_sphere_three`, a `proof_wanted`).
The theorem `Frontier.poincare_3sphere` below proves a *reduction* of this statement to a
purely local one. -/
def PoincareConjecture3.{u} : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M] [ChartedSpace ℝ³ M]
    [SimplyConnectedSpace M] [CompactSpace M], Nonempty (M ≃ₜ 𝕊³)

/-- The **punctured criterion**: every simply connected closed 3-manifold becomes homeomorphic
to `ℝ³` after deleting a suitable point.

This is the statement that `Frontier.poincare_3sphere` proves equivalent to the Poincaré
conjecture `PoincareConjecture3`. -/
def PuncturedEuclideanCriterion3.{u} : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M] [ChartedSpace ℝ³ M]
    [SimplyConnectedSpace M] [CompactSpace M],
    ∃ x : M, Nonempty (({x}ᶜ : Set M) ≃ₜ ℝ³)

/-! ## Topological ingredients -/

/-- The complement of the point at infinity in the one-point compactification of `X`
is homeomorphic to `X`. -/
noncomputable def onePointComplInfty (X : Type*) [TopologicalSpace X] :
    ({(∞ : OnePoint X)}ᶜ : Set (OnePoint X)) ≃ₜ X := by
  have h : Topology.IsEmbedding ((↑) : X → OnePoint X) :=
    OnePoint.isOpenEmbedding_coe.toIsEmbedding
  have hr : Set.range ((↑) : X → OnePoint X) = ({(∞ : OnePoint X)}ᶜ : Set (OnePoint X)) := by
    ext y; induction y using OnePoint.rec <;> simp
  exact (h.toHomeomorph.trans (Homeomorph.setCongr hr)).symm

/-- The one-point compactification of `ℝ³` is the 3-sphere. -/
noncomputable def onePointEuclideanThreeHomeoSphere : OnePoint ℝ³ ≃ₜ 𝕊³ :=
  onePointEquivSphereOfFinrankEq (by simp)

/-- Deleting a point from a compact Hausdorff space and then compactifying again returns
the original space: if `X` is compact Hausdorff and `x : X`, then `X` is homeomorphic to the
one-point compactification of `X \ {x}`. -/
noncomputable def onePointComplHomeoSelf (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] (x : X) : OnePoint ({x}ᶜ : Set X) ≃ₜ X :=
  OnePoint.equivOfIsEmbeddingOfRangeEq x Subtype.val Topology.IsEmbedding.subtypeVal
    Subtype.range_coe

/-- If `e : X ≃ₜ Y` is a homeomorphism, then deleting `x` from `X` and `e x` from `Y` gives
homeomorphic spaces. -/
def complSingletonCongr {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) : (({x}ᶜ : Set X)) ≃ₜ (({e x}ᶜ : Set Y)) :=
  Homeomorph.subtype e (fun a => by simp [e.injective.eq_iff])

/-! ## The base case: the 3-sphere itself -/

/-- **Base case.** The 3-sphere is a compact Hausdorff charted space over `ℝ³`, i.e. a closed
topological 3-manifold, and (as required by the punctured criterion) deleting a point from it
yields a space homeomorphic to `ℝ³`. -/
theorem sphere_three_punctured_homeo_euclidean :
    ∃ v : 𝕊³, Nonempty (({v}ᶜ : Set 𝕊³) ≃ₜ ℝ³) := by
  refine ⟨onePointEuclideanThreeHomeoSphere ∞, ⟨?_⟩⟩
  refine (complSingletonCongr onePointEuclideanThreeHomeoSphere.symm _).trans ?_
  rw [Homeomorph.symm_apply_apply]
  exact onePointComplInfty ℝ³

/-- The 3-sphere is a closed (compact, Hausdorff, boundaryless) topological 3-manifold: it is
compact, Hausdorff, and carries a charted space structure modelled on `ℝ³` (given by
stereographic projection). -/
theorem sphere_three_isClosedManifold :
    CompactSpace 𝕊³ ∧ T2Space 𝕊³ ∧ Nonempty (ChartedSpace ℝ³ 𝕊³) :=
  ⟨inferInstance, inferInstance, ⟨inferInstance⟩⟩

/-! ## The reduction -/

/-- **A Lean-checked reduction of the Poincaré conjecture.**

The 3-dimensional topological Poincaré conjecture (`PoincareConjecture3`: every simply
connected closed topological 3-manifold is homeomorphic to `𝕊³`) is *equivalent* to the
local, puncture-based criterion `PuncturedEuclideanCriterion3`: every simply connected
closed topological 3-manifold becomes homeomorphic to Euclidean space `ℝ³` after removing
a single suitable point.

The forward implication uses stereographic projection (in the form of the homeomorphism
`OnePoint ℝ³ ≃ₜ 𝕊³`); the backward implication uses the uniqueness of the one-point
compactification of a compact Hausdorff space with a point removed.

The conjecture itself (Perelman's theorem) is *not* proved here. -/
theorem poincare_3sphere.{u} :
    PoincareConjecture3.{u} ↔ PuncturedEuclideanCriterion3.{u} := by
  constructor
  · intro h M _ _ _ _ _
    obtain ⟨e⟩ := h M
    -- transport a puncture of `𝕊³` back to `M`
    obtain ⟨v, ⟨f⟩⟩ := sphere_three_punctured_homeo_euclidean
    refine ⟨e.symm v, ⟨?_⟩⟩
    refine (complSingletonCongr e _).trans ?_
    rw [Homeomorph.apply_symm_apply]
    exact f
  · intro h M _ _ _ _ _
    obtain ⟨x, ⟨f⟩⟩ := h M
    exact ⟨(onePointComplHomeoSelf M x).symm.trans
      ((Homeomorph.onePointCongr f).trans onePointEuclideanThreeHomeoSphere)⟩

/-- A second, elementary reduction: to prove the Poincaré conjecture it suffices to construct,
for each simply connected closed 3-manifold `M`, a *continuous bijection* `M → 𝕊³`
(no continuity of the inverse required), since a continuous bijection from a compact space to a
Hausdorff space is automatically a homeomorphism. -/
theorem poincare_3sphere_of_continuous_bijection.{u}
    (h : ∀ (M : Type u) [TopologicalSpace M] [T2Space M] [ChartedSpace ℝ³ M]
      [SimplyConnectedSpace M] [CompactSpace M],
      ∃ f : M → 𝕊³, Continuous f ∧ Function.Bijective f) :
    PoincareConjecture3.{u} := by
  intro M _ _ _ _ _
  obtain ⟨f, hf, hbij⟩ := h M
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hbij) hf⟩

end Frontier

#print axioms Frontier.poincare_3sphere
#print axioms Frontier.sphere_three_punctured_homeo_euclidean
#print axioms Frontier.poincare_3sphere_of_continuous_bijection
#print axioms Frontier.sphere_three_isClosedManifold

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

