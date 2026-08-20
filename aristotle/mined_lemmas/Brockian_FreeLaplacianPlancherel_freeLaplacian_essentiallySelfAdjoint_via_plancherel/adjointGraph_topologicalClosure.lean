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

/-
/-!
# Free Laplacian Essentially Self Adjoint Via Plancherel
Category: Brockian (Open Discharge)
Target: Brockian.FreeLaplacianPlancherel.freeLaplacian_essentiallySelfAdjoint_via_plancherel
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

open MeasureTheory SchwartzMap FourierTransform Complex
open scoped ComplexInnerProductSpace

namespace Brockian.FreeLaplacianPlancherel

/-! ## Abstract theory of graphs of unbounded operators -/

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The graph of the adjoint of the (not necessarily bounded) operator whose graph is `G`:
the set of pairs `(g, h)` with `⟪T f, g⟫ = ⟪f, h⟫` for all `(f, T f) ∈ G`. -/

lemma adjointGraph_topologicalClosure (G : Submodule ℂ (H × H)) :
    adjointGraph G.topologicalClosure = adjointGraph G := by
  apply le_antisymm
  · intro q hq p hp
    exact hq p (G.le_topologicalClosure hp)
  · intro q hq p hp
    have hsub : (G : Set (H × H)) ⊆ {p : H × H | ⟪p.2, q.1⟫ = ⟪p.1, q.2⟫} := fun r hr => hq r hr
    have hclosed : IsClosed {p : H × H | ⟪p.2, q.1⟫ = ⟪p.1, q.2⟫} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    have := closure_minimal hsub hclosed
    exact this (by rwa [← Submodule.topologicalClosure_coe])

omit [CompleteSpace H] in
/-- Symmetry extends from a graph to its closure. -/
