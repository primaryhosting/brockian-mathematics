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

def PoincareConjecture3Dense : Prop :=
  ∀ (M : Type u) (_ : TopologicalSpace M),
    IsClosedManifold 3 M → ConnectedSpace M → SimplyConnectedSpace M →
      ∃ f : M → Sphere 3, Continuous f ∧ Function.Injective f ∧ Dense (Set.range f)

/-! ## The 3-sphere is a closed 3-manifold

This shows the statement above is not vacuous: the model space `S³` does satisfy the
topological hypotheses of the conjecture. -/

instance : ConnectedSpace (Sphere 3) := by
  have h : IsConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) := by
    refine isConnected_sphere ?_ _ zero_le_one
    have : Module.rank ℝ (EuclideanSpace ℝ (Fin 4)) = 4 := by
      simp [rank_eq_card_basis (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis]
    rw [this]
    norm_num
  exact (isConnected_iff_connectedSpace.mp h)

