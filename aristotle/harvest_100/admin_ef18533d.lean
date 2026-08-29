/-
# Poincare 3 Sphere
Category: Frontier — Moonshot
Target: Frontier.poincare_3sphere
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Poincare 3 Sphere
Category: Frontier — Moonshot
Target: Frontier.poincare_3sphere
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

open Metric Set Topology Module

namespace Frontier

universe u

/-- The 3-sphere, realized as the unit sphere in 4-dimensional Euclidean space. -/
abbrev Sphere3 : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

/-- `M` is a *closed 3-manifold*: a compact, Hausdorff, second countable space which is
locally homeomorphic to `ℝ³` (equivalently, a compact 3-manifold without boundary). -/
def IsClosedThreeManifold (M : Type u) [TopologicalSpace M] : Prop :=
  CompactSpace M ∧ T2Space M ∧ SecondCountableTopology M ∧
    ∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      Nonempty (U ≃ₜ EuclideanSpace ℝ (Fin 3))

/-- **The Poincaré conjecture** (Perelman): every simply-connected closed 3-manifold is
homeomorphic to the 3-sphere. -/
def Poincare3Conjecture : Prop :=
  ∀ (M : Type u) [TopologicalSpace M], IsClosedThreeManifold M → SimplyConnectedSpace M →
    Nonempty (M ≃ₜ Sphere3)

/-- **The punctured-sphere criterion**: every simply-connected closed 3-manifold has a point
whose complement is homeomorphic to `ℝ³`. -/
def PuncturedCriterion : Prop :=
  ∀ (M : Type u) [TopologicalSpace M], IsClosedThreeManifold M → SimplyConnectedSpace M →
    ∃ p : M, Nonempty ({x : M // x ≠ p} ≃ₜ EuclideanSpace ℝ (Fin 3))

/-! ### One-point compactification lemmas -/

/-- A compact Hausdorff space is the one-point compactification of the complement of any of
its points. -/
noncomputable def onePointComplHomeomorph {M : Type u} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] (p : M) : OnePoint {x : M // x ≠ p} ≃ₜ M :=
  OnePoint.equivOfIsEmbeddingOfRangeEq p Subtype.val Topology.IsEmbedding.subtypeVal
    (by ext x; simp)

/-- If some point of a compact Hausdorff space `M` has complement homeomorphic to `ℝ³`, then
`M` is homeomorphic to the 3-sphere. -/
noncomputable def homeomorphSphere3OfPunctured {M : Type u} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] {p : M} (e : {x : M // x ≠ p} ≃ₜ EuclideanSpace ℝ (Fin 3)) :
    M ≃ₜ Sphere3 :=
  (onePointComplHomeomorph p).symm.trans
    (e.onePointCongr.trans (onePointEquivSphereOfFinrankEq (ι := Fin 4) (by simp)))

/-! ### The punctured 3-sphere is `ℝ³` -/

instance : Fact (finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩

/-- Stereographic projection: the complement of a point in the 3-sphere is homeomorphic to
`ℝ³`. -/
noncomputable def spherePuncturedHomeomorph (v : Sphere3) :
    {x : Sphere3 // x ≠ v} ≃ₜ EuclideanSpace ℝ (Fin 3) :=
  let e := stereographic' 3 v
  (Homeomorph.setCongr (s := {x : Sphere3 | x ≠ v}) (t := e.source)
      (by rw [stereographic'_source]; rfl)).trans
    (e.toHomeomorphSourceTarget.trans
      ((Homeomorph.setCongr (stereographic'_target v)).trans (Homeomorph.Set.univ _)))

/-! ### The 3-sphere is a closed 3-manifold -/

theorem sphere3_isClosedThreeManifold : IsClosedThreeManifold Sphere3 := by
  refine ⟨inferInstance, inferInstance, inferInstance, fun x => ?_⟩
  refine ⟨{y : Sphere3 | y ≠ -x}, isOpen_compl_singleton, ?_, ⟨?_⟩⟩
  · have hx : (x : EuclideanSpace ℝ (Fin 4)) ≠ 0 := by
      intro h
      have := x.2
      simp [h] at this
    simp only [Set.mem_setOf_eq, ne_eq]
    intro h
    apply hx
    have : (x : EuclideanSpace ℝ (Fin 4)) = -(x : EuclideanSpace ℝ (Fin 4)) := congrArg Subtype.val h
    linear_combination (norm := module) (2⁻¹ : ℝ) • this
  · exact spherePuncturedHomeomorph (-x)

/-- Pointwise form of the reduction: a closed 3-manifold with a point whose complement is
homeomorphic to `ℝ³` is homeomorphic to the 3-sphere. (Simple connectedness is not needed:
it is only used to produce such a point.) -/
theorem nonempty_homeomorph_sphere3_of_punctured (M : Type u) [TopologicalSpace M]
    (hM : IsClosedThreeManifold M) (p : M)
    (h : Nonempty ({x : M // x ≠ p} ≃ₜ EuclideanSpace ℝ (Fin 3))) :
    Nonempty (M ≃ₜ Sphere3) := by
  obtain ⟨hcomp, ht2, -, -⟩ := hM
  obtain ⟨e⟩ := h
  exact ⟨homeomorphSphere3OfPunctured e⟩

/-- The hypothesis of the reduction is satisfiable: the 3-sphere is a closed 3-manifold which
has a point whose complement is homeomorphic to `ℝ³`. -/
theorem sphere3_exists_punctured_homeomorph_euclidean :
    ∃ p : Sphere3, Nonempty ({x : Sphere3 // x ≠ p} ≃ₜ EuclideanSpace ℝ (Fin 3)) :=
  ⟨⟨EuclideanSpace.single 0 1, by simp⟩, ⟨spherePuncturedHomeomorph _⟩⟩

/-! ### The reduction -/

/-- **Lean-checked reduction of the Poincaré conjecture.**

The Poincaré conjecture — every simply-connected closed 3-manifold is homeomorphic to `S³` —
is *equivalent* to the punctured-sphere criterion: every simply-connected closed 3-manifold has
a point whose complement is homeomorphic to `ℝ³`.

The nontrivial direction proved here (`←`) is the reduction proper: it upgrades a purely local
statement (one puncture is Euclidean) to a global homeomorphism with `S³`, via the uniqueness of
the one-point compactification of a compact Hausdorff space and the identification of the
one-point compactification of `ℝ³` with `S³` (stereographic projection). The direction (`→`)
uses that the 3-sphere itself is a closed 3-manifold with punctures homeomorphic to `ℝ³`. -/
theorem poincare_3sphere : Poincare3Conjecture.{u} ↔ PuncturedCriterion.{u} := by
  constructor
  · intro h M _ hM hsc
    obtain ⟨e⟩ := h M hM hsc
    refine ⟨e.symm ⟨EuclideanSpace.single 0 1, by simp⟩, ⟨?_⟩⟩
    exact (e.subtype (q := fun y : Sphere3 => y ≠ ⟨EuclideanSpace.single 0 1, by simp⟩)
        (fun x => by
          constructor
          · exact fun hx h' => hx (by rw [← h', e.symm_apply_apply])
          · exact fun hx h' => hx (by rw [h', e.apply_symm_apply]))).trans
      (spherePuncturedHomeomorph _)
  · intro h M _ hM hsc
    obtain ⟨p, hp⟩ := h M hM hsc
    exact nonempty_homeomorph_sphere3_of_punctured M hM p hp

end Frontier

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

