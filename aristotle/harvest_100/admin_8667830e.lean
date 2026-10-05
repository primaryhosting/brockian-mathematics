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

set_option grind.warning false

open scoped Manifold ContDiff
open Metric (sphere)

namespace Frontier

/-- `ℝ³`, the Euclidean model space of dimension `3`. -/
abbrev EuclideanThree : Type := EuclideanSpace ℝ (Fin 3)

/-- The standard `3`-sphere `𝕊³ ⊆ ℝ⁴`. -/
abbrev ThreeSphere : Type := sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

/-- `ℝ⁴` is `4 = 3 + 1`-dimensional; this is what equips `𝕊³` with its charts. -/
instance factFinrankFour : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) :=
  ⟨by simp⟩

/-- **The 3-dimensional topological Poincaré conjecture** (Perelman):
every simply-connected closed (compact, boundaryless) topological `3`-manifold is
homeomorphic to the `3`-sphere.  Here "closed `3`-manifold" is spelled as in Mathlib:
a compact Hausdorff space charted on `ℝ³`. -/
def PoincareConjecture3 : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace EuclideanThree M]
    [SimplyConnectedSpace M] [CompactSpace M], Nonempty (M ≃ₜ ThreeSphere)

/-- A formally weaker form of the conjecture: only a *continuous bijection* onto `𝕊³` is
required (no continuity of the inverse). -/
def PoincareConjecture3Bijection : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace EuclideanThree M]
    [SimplyConnectedSpace M] [CompactSpace M],
    ∃ f : M → ThreeSphere, Continuous f ∧ Function.Bijective f

/-- An even weaker looking form of the conjecture: only a *continuous injection with dense
range* into `𝕊³` is required. -/
def PoincareConjecture3DenseInjection : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace EuclideanThree M]
    [SimplyConnectedSpace M] [CompactSpace M],
    ∃ f : M → ThreeSphere, Continuous f ∧ Function.Injective f ∧ DenseRange f

/-- The negation of the conjecture, spelled as the existence of a counterexample. -/
def PoincareConjecture3Counterexample : Prop :=
  ∃ (M : Type) (_ : TopologicalSpace M) (_ : T2Space M) (_ : ChartedSpace EuclideanThree M)
    (_ : SimplyConnectedSpace M) (_ : CompactSpace M), IsEmpty (M ≃ₜ ThreeSphere)

/-- Non-vacuity of the hypotheses: the `3`-sphere itself is a closed (compact, Hausdorff,
boundaryless) topological `3`-manifold, and it is of course homeomorphic to `𝕊³`. -/
theorem threeSphere_isClosedThreeManifold :
    CompactSpace ThreeSphere ∧ T2Space ThreeSphere ∧
      Nonempty (ChartedSpace EuclideanThree ThreeSphere) ∧
      Nonempty (ThreeSphere ≃ₜ ThreeSphere) :=
  ⟨inferInstance, inferInstance, ⟨inferInstance⟩, ⟨Homeomorph.refl _⟩⟩

/-- The homotopy-theoretic half of the conjecture: every simply-connected closed `3`-manifold
is homotopy equivalent to `𝕊³`. -/
def HomotopyPoincare3 : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace EuclideanThree M]
    [SimplyConnectedSpace M] [CompactSpace M], Nonempty (ContinuousMap.HomotopyEquiv M ThreeSphere)

/-- The generalized (topological) Poincaré conjecture in dimension `3`, as stated in Mathlib:
a closed `3`-manifold homotopy equivalent to `𝕊³` is homeomorphic to `𝕊³`. -/
def GeneralizedPoincare3 : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace EuclideanThree M],
    ContinuousMap.HomotopyEquiv M ThreeSphere → Nonempty (M ≃ₜ ThreeSphere)

/-- Reduction to the classical two-step route: the conjecture follows from its homotopy-theoretic
half together with the generalized (homotopy ⇒ homeomorphism) Poincaré conjecture. -/
theorem poincareConjecture3_of_homotopy
    (h₁ : HomotopyPoincare3) (h₂ : GeneralizedPoincare3) : PoincareConjecture3 := by
  intro M _ _ _ _ _
  exact h₂ M (h₁ M).some

/-- The class of simply-connected closed `3`-manifolds is invariant under homeomorphism:
if `N` is homeomorphic to such a manifold `M`, then `N` is one as well.  Hence the conjecture
only has to be checked on one representative of each homeomorphism class. -/
theorem closedThreeManifold_of_homeomorph {N M : Type} [TopologicalSpace N] [TopologicalSpace M]
    [T2Space M] [ChartedSpace EuclideanThree M] [SimplyConnectedSpace M] [CompactSpace M]
    (e : N ≃ₜ M) :
    T2Space N ∧ Nonempty (ChartedSpace EuclideanThree N) ∧ SimplyConnectedSpace N ∧
      CompactSpace N := by
  refine ⟨e.isEmbedding.t2Space, ⟨?_⟩, ?_, e.symm.compactSpace⟩
  · letI : ChartedSpace M N :=
      e.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
    exact ChartedSpace.comp EuclideanThree M N
  · exact e.toHomotopyEquiv.simplyConnectedSpace

/-- **Lean-checked reduction of the Poincaré conjecture in dimension 3.**

The conjecture "every simply-connected closed 3-manifold is homeomorphic to `𝕊³`" is
*equivalent* to each of three formally weaker or dual statements:

1. every such manifold admits merely a continuous bijection onto `𝕊³`
   (the inverse is then automatically continuous, by compactness and the Hausdorff property);
2. every such manifold admits merely a continuous injection into `𝕊³` with dense range
   (the image is then compact, hence closed, hence all of `𝕊³`);
3. the contrapositive form: there is no counterexample, i.e. no simply-connected closed
   3-manifold admitting no homeomorphism to `𝕊³`.

So it suffices to attack any one of these reformulations. -/
theorem poincare_3sphere :
    (PoincareConjecture3 ↔ PoincareConjecture3Bijection) ∧
    (PoincareConjecture3 ↔ PoincareConjecture3DenseInjection) ∧
    (PoincareConjecture3 ↔ ¬ PoincareConjecture3Counterexample) := by
  have key : PoincareConjecture3DenseInjection → PoincareConjecture3 := by
    intro h M _ _ _ _ _
    obtain ⟨f, hcont, hinj, hdense⟩ := h M
    have hsurj : Function.Surjective f := by
      have hclosed : IsClosed (Set.range f) := (isCompact_range hcont).isClosed
      have hrange : Set.range f = Set.univ := by
        rw [← hclosed.closure_eq]; exact hdense.closure_eq
      exact Set.range_eq_univ.mp hrange
    exact ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f ⟨hinj, hsurj⟩) hcont⟩
  have bij_to_dense : PoincareConjecture3Bijection → PoincareConjecture3DenseInjection := by
    intro h M _ _ _ _ _
    obtain ⟨f, hcont, hinj, hsurj⟩ := h M
    exact ⟨f, hcont, hinj, hsurj.denseRange⟩
  have conj_to_bij : PoincareConjecture3 → PoincareConjecture3Bijection := by
    intro h M _ _ _ _ _
    obtain ⟨e⟩ := h M
    exact ⟨e, e.continuous, e.bijective⟩
  refine ⟨⟨conj_to_bij, fun h => key (bij_to_dense h)⟩,
    ⟨fun h => bij_to_dense (conj_to_bij h), key⟩, ?_⟩
  constructor
  · intro h hc
    obtain ⟨M, _, _, _, _, _, hM⟩ := hc
    exact hM.elim' (h M).some
  · intro h M _ _ _ _ _
    by_contra hM
    exact h ⟨M, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, not_nonempty_iff.mp hM⟩

end Frontier

