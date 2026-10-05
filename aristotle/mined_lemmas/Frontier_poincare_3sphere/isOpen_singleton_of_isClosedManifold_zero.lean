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

theorem isOpen_singleton_of_isClosedManifold_zero {M : Type u} [TopologicalSpace M]
    (h : IsClosedManifold 0 M) (x : M) : IsOpen ({x} : Set M) := by
  obtain ⟨-, -, ⟨hchart⟩⟩ := h
  letI := hchart
  have hsub : Subsingleton (EuclideanSpace ℝ (Fin 0)) := inferInstance
  set c := chartAt (EuclideanSpace ℝ (Fin 0)) x with hc
  have hxs : x ∈ c.source := mem_chart_source _ x
  have hss : c.source ⊆ ({x} : Set M) := by
    intro y hy
    have : c y = c x := Subsingleton.elim _ _
    exact c.injOn hy hxs this
  have hxsub : ({x} : Set M) ⊆ c.source := by
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    exact hy ▸ hxs
  have : ({x} : Set M) = c.source := Set.Subset.antisymm hxsub hss
  rw [this]
  exact c.open_source

/-- **Base case of the classification.**  Every connected closed `0`-manifold is
homeomorphic to a point. -/
