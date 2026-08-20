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
