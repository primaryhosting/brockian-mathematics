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
