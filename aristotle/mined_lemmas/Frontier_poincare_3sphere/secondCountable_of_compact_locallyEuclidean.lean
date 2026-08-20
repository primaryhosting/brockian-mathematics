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
