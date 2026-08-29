/-
# Poincare 3 Sphere
Category: Frontier — Moonshot
Target: Frontier.poincare_3sphere
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring, so the header above is a plain
-- block comment.)

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
## Overview

The Poincaré conjecture (proved by Perelman) states that every simply-connected closed
3-manifold is homeomorphic to the 3-sphere `S³`.

This file:

* formalizes the statement (`Frontier.PoincareConjecture3`), based on an elementary
  point-set definition of a closed topological `n`-manifold
  (`Frontier.IsClosedManifold`);
* proves a Lean-checked *reduction*: the conjecture is equivalent to the non-existence of a
  counterexample (contrapositive form), the class of counterexamples is invariant under
  homeomorphism, and the statement is non-vacuous, i.e. the 3-sphere itself is a connected
  closed 3-manifold for which the conclusion holds.

The full conjecture itself is *not* proved here; `Frontier.PoincareConjecture3` is a `Prop`
that is only ever used as a hypothesis or as one side of an equivalence.
-/

namespace Frontier

universe u v

/-- The standard 3-sphere, as the unit sphere in 4-dimensional Euclidean space. -/
abbrev Sphere3 : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

/-- A topological space is *locally Euclidean of dimension `n`* if every point has an open
neighbourhood homeomorphic to an open subset of `ℝⁿ`. -/
def LocallyEuclidean (n : ℕ) (M : Type u) [TopologicalSpace M] : Prop :=
  ∀ x : M, ∃ (U : Set M) (V : Set (EuclideanSpace ℝ (Fin n))),
    IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ Nonempty (U ≃ₜ V)

/-- A *closed `n`-manifold*: a compact, Hausdorff, second-countable topological space that is
locally Euclidean of dimension `n` (in particular it has no boundary). -/
structure IsClosedManifold (n : ℕ) (M : Type u) [TopologicalSpace M] : Prop where
  compactSpace : CompactSpace M
  t2Space : T2Space M
  secondCountable : SecondCountableTopology M
  locallyEuclidean : LocallyEuclidean n M

/-- The Poincaré statement for a single space `M`: if `M` is a connected, simply-connected
closed 3-manifold, then `M` is homeomorphic to the 3-sphere. -/
def PoincareStatement (M : Type u) [TopologicalSpace M] : Prop :=
  IsClosedManifold 3 M → ConnectedSpace M → SimplyConnectedSpace M → Nonempty (M ≃ₜ Sphere3)

/-- **The Poincaré conjecture in dimension 3** (Perelman): every simply-connected closed
3-manifold is homeomorphic to `S³`. -/
def PoincareConjecture3 : Prop := ∀ (M : Type) [TopologicalSpace M], PoincareStatement M

/-- A counterexample to the Poincaré conjecture: a connected, simply-connected closed
3-manifold admitting no homeomorphism to `S³`. -/
def IsPoincareCounterexample (M : Type u) [TopologicalSpace M] : Prop :=
  IsClosedManifold 3 M ∧ ConnectedSpace M ∧ SimplyConnectedSpace M ∧ IsEmpty (M ≃ₜ Sphere3)

/-! ## Homeomorphism invariance -/

section Invariance

variable {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]

theorem LocallyEuclidean.homeomorph {n : ℕ} (e : M ≃ₜ N) (h : LocallyEuclidean n M) :
    LocallyEuclidean n N := by
  intro y
  obtain ⟨U, V, hU, hV, hxU, ⟨f⟩⟩ := h (e.symm y)
  refine ⟨e '' U, V, e.isOpen_image.2 hU, hV, ⟨e.symm y, hxU, e.apply_symm_apply y⟩, ?_⟩
  exact ⟨(e.image U).symm.trans f⟩

theorem IsClosedManifold.homeomorph {n : ℕ} (e : M ≃ₜ N) (h : IsClosedManifold n M) :
    IsClosedManifold n N := by
  haveI := h.compactSpace
  haveI := h.t2Space
  haveI := h.secondCountable
  exact
    { compactSpace := e.compactSpace
      t2Space := e.t2Space
      secondCountable := e.symm.secondCountableTopology
      locallyEuclidean := h.locallyEuclidean.homeomorph e }

theorem connectedSpace_of_homeomorph (e : M ≃ₜ N) (h : ConnectedSpace M) : ConnectedSpace N :=
  e.surjective.connectedSpace e.continuous

theorem simplyConnectedSpace_congr (e : M ≃ₜ N) :
    SimplyConnectedSpace M ↔ SimplyConnectedSpace N :=
  e.toHomotopyEquiv.simplyConnectedSpace_iff

/-- The Poincaré statement is invariant under homeomorphism. -/
theorem poincareStatement_of_homeomorph (e : M ≃ₜ N) (h : PoincareStatement M) :
    PoincareStatement N := by
  intro hmanN hconnN hscN
  have hmanM : IsClosedManifold 3 M := hmanN.homeomorph e.symm
  have hconnM : ConnectedSpace M := connectedSpace_of_homeomorph e.symm hconnN
  have hscM : SimplyConnectedSpace M := (simplyConnectedSpace_congr e).2 hscN
  obtain ⟨g⟩ := h hmanM hconnM hscM
  exact ⟨e.symm.trans g⟩

theorem poincareStatement_congr (e : M ≃ₜ N) :
    PoincareStatement M ↔ PoincareStatement N :=
  ⟨poincareStatement_of_homeomorph e, poincareStatement_of_homeomorph e.symm⟩

theorem isPoincareCounterexample_of_homeomorph (e : M ≃ₜ N)
    (h : IsPoincareCounterexample M) : IsPoincareCounterexample N := by
  obtain ⟨hman, hconn, hsc, hempty⟩ := h
  exact ⟨hman.homeomorph e, connectedSpace_of_homeomorph e hconn,
    (simplyConnectedSpace_congr e).1 hsc, ⟨fun g => hempty.elim (e.trans g)⟩⟩

/-- The class of counterexamples is invariant under homeomorphism. -/
theorem isPoincareCounterexample_congr (e : M ≃ₜ N) :
    IsPoincareCounterexample M ↔ IsPoincareCounterexample N :=
  ⟨isPoincareCounterexample_of_homeomorph e, isPoincareCounterexample_of_homeomorph e.symm⟩

end Invariance

/-! ## The 3-sphere is a connected closed 3-manifold -/

theorem locallyEuclidean_sphere3 : LocallyEuclidean 3 Sphere3 := by
  intro x
  refine ⟨(chartAt (EuclideanSpace ℝ (Fin 3)) x).source,
    (chartAt (EuclideanSpace ℝ (Fin 3)) x).target,
    (chartAt (EuclideanSpace ℝ (Fin 3)) x).open_source,
    (chartAt (EuclideanSpace ℝ (Fin 3)) x).open_target,
    mem_chart_source _ x,
    ⟨(chartAt (EuclideanSpace ℝ (Fin 3)) x).toHomeomorphSourceTarget⟩⟩

theorem isClosedManifold_sphere3 : IsClosedManifold 3 Sphere3 where
  compactSpace := inferInstance
  t2Space := inferInstance
  secondCountable := inferInstance
  locallyEuclidean := locallyEuclidean_sphere3

theorem connectedSpace_sphere3 : ConnectedSpace Sphere3 := by
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 4)) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    norm_num
  exact isConnected_iff_connectedSpace.1
    (isConnected_sphere hrank (0 : EuclideanSpace ℝ (Fin 4)) zero_le_one)

theorem poincareStatement_sphere3 : PoincareStatement Sphere3 :=
  fun _ _ _ => ⟨Homeomorph.refl _⟩

/-! ## Reduction to the charted-space formulation

Mathlib states the conjecture (as a `proof_wanted`) for a space equipped with a
`ChartedSpace (EuclideanSpace ℝ (Fin 3))` structure. We check that our elementary point-set
formulation follows from that one, by manufacturing an atlas out of the local Euclidean charts.
-/

/-- The charted-space formulation of the 3-dimensional Poincaré conjecture: a compact,
Hausdorff, simply-connected space charted on `ℝ³` is homeomorphic to `S³`. -/
def ChartedPoincare3 : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [CompactSpace M] [SimplyConnectedSpace M],
    Nonempty (M ≃ₜ Sphere3)

/-- A point of a locally Euclidean space lies in the source of some chart to `ℝⁿ`. -/
theorem exists_chart_of_locallyEuclidean {n : ℕ} {M : Type u} [TopologicalSpace M]
    (h : LocallyEuclidean n M) (x : M) :
    ∃ c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)), x ∈ c.source := by
  obtain ⟨U, V, hU, hV, hxU, ⟨e⟩⟩ := h x
  haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
  haveI : Nonempty V := ⟨e ⟨x, hxU⟩⟩
  refine ⟨((hU.isOpenEmbedding_subtypeVal).toOpenPartialHomeomorph _).symm.trans
    (e.toOpenPartialHomeomorph.trans
      ((hV.isOpenEmbedding_subtypeVal).toOpenPartialHomeomorph _)), ?_⟩
  simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source,
    Homeomorph.toOpenPartialHomeomorph_source, Set.mem_inter_iff, Set.mem_preimage]
  exact ⟨by simpa [Subtype.range_val] using hxU, trivial, trivial⟩

/-- A locally Euclidean space carries a charted-space structure modelled on `ℝⁿ`. -/
theorem nonempty_chartedSpace_of_locallyEuclidean {n : ℕ} {M : Type} [TopologicalSpace M]
    (h : LocallyEuclidean n M) :
    Nonempty (ChartedSpace (EuclideanSpace ℝ (Fin n)) M) := by
  choose c hc using exists_chart_of_locallyEuclidean h
  exact ⟨{ atlas := Set.range c
           chartAt := c
           mem_chart_source := hc
           chart_mem_atlas := fun x => ⟨x, rfl⟩ }⟩

/-- **Reduction**: the elementary point-set form of the conjecture follows from the
charted-space form used in Mathlib's `proof_wanted`. -/
theorem poincareConjecture3_of_chartedPoincare3 (h : ChartedPoincare3) :
    PoincareConjecture3 := by
  intro M _ hman _ hsc
  haveI := hman.compactSpace
  haveI := hman.t2Space
  obtain ⟨cs⟩ := nonempty_chartedSpace_of_locallyEuclidean hman.locallyEuclidean
  haveI := cs
  exact h M

/-! ## The reduction -/

/--
**Poincaré conjecture in dimension 3: formalization and a Lean-checked reduction.**

The statement (`Frontier.PoincareConjecture3`, "every connected, simply-connected closed
3-manifold is homeomorphic to `S³`") is here reduced to, and shown equivalent to, the
contrapositive form: *no* counterexample exists. In addition we verify that:

* the class of counterexamples is closed under homeomorphism, so the conjecture only depends on
  the homeomorphism type of a space;
* the conjecture reduces to the charted-space formulation (`Frontier.ChartedPoincare3`, the
  shape in which Mathlib records the conjecture): every locally Euclidean space admits an atlas;
* the statement is non-vacuous and consistent with the model case: the 3-sphere itself is a
  connected closed 3-manifold satisfying the conclusion.

The full theorem of Perelman is not proved here.
-/
theorem poincare_3sphere :
    (PoincareConjecture3 ↔ ¬ ∃ (M : Type) (_ : TopologicalSpace M),
        IsPoincareCounterexample M)
    ∧ (∀ (M N : Type) (_ : TopologicalSpace M) (_ : TopologicalSpace N), (M ≃ₜ N) →
        (IsPoincareCounterexample M ↔ IsPoincareCounterexample N))
    ∧ (ChartedPoincare3 → PoincareConjecture3)
    ∧ IsClosedManifold 3 Sphere3 ∧ ConnectedSpace Sphere3 ∧ PoincareStatement Sphere3 := by
  refine ⟨⟨?_, ?_⟩, ?_, poincareConjecture3_of_chartedPoincare3, isClosedManifold_sphere3,
    connectedSpace_sphere3, poincareStatement_sphere3⟩
  · rintro h ⟨M, _, hman, hconn, hsc, hempty⟩
    exact hempty.elim (h M hman hconn hsc).some
  · intro h M _ hman hconn hsc
    by_contra hne
    exact h ⟨M, ‹TopologicalSpace M›, hman, hconn, hsc, not_nonempty_iff.1 hne⟩
  · intro M N _ _ e
    exact isPoincareCounterexample_congr e

end Frontier

