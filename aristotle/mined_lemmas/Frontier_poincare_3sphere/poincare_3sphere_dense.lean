/-
# Poincare 3 Sphere
Category: Frontier — Moonshot
Target: Frontier.poincare_3sphere
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
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

universe u

/-! ## Formalizing the statement

We formalize "closed `n`-manifold" as: a compact Hausdorff space which is locally
homeomorphic to `ℝⁿ` (i.e. carries a `ChartedSpace (EuclideanSpace ℝ (Fin n))`
structure).  "Closed" here means compact and without boundary, as usual.
-/

/-- `IsClosedManifold n M` says that the topological space `M` is a closed
(= compact, boundaryless) topological `n`-manifold: it is compact, Hausdorff and
locally homeomorphic to `EuclideanSpace ℝ (Fin n)`. -/

theorem poincare_3sphere_dense : PoincareConjecture3.{u} ↔ PoincareConjecture3Dense.{u} := by
  constructor
  · intro h M _ hM hconn hsc
    obtain ⟨e⟩ := h M ‹_› hM hconn hsc
    refine ⟨e, e.continuous, e.injective, ?_⟩
    rw [e.surjective.range_eq]
    exact dense_univ
  · intro h M _ hM hconn hsc
    obtain ⟨f, hf, hinj, hdense⟩ := h M ‹_› hM hconn hsc
    haveI : CompactSpace M := hM.1
    have hclosed : IsClosed (Set.range f) := (isCompact_range hf).isClosed
    have hrange : Set.range f = Set.univ := hclosed.closure_eq ▸ hdense.closure_eq
    exact homeomorph_of_continuous_bijective hf ⟨hinj, Set.range_eq_univ.mp hrange⟩

/-! ## The base case: closed 0-manifolds

The classification of closed connected `n`-manifolds in dimension `0`: a connected closed
`0`-manifold is a point.  (In dimension `0` the sphere `S⁰` is the two-point space, so the
connected model is `PUnit`.)  This is the base case of the classification programme of
which the Poincaré conjecture is the dimension-3 instance. -/

/-- In a closed `0`-manifold every singleton is open. -/
