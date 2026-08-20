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

lemma inner_symm_of_mem_closure {G : Submodule ℂ (H × H)} (hsym : IsSymmetricGraph G)
    {p q : H × H} (hp : p ∈ G.topologicalClosure) (hq : q ∈ G.topologicalClosure) :
    ⟪p.2, q.1⟫ = ⟪p.1, q.2⟫ := by
  have hcl : G.topologicalClosure ≤ adjointGraph G :=
    Submodule.topologicalClosure_minimal _ hsym (isClosed_adjointGraph G)
  have hq' : q ∈ adjointGraph G.topologicalClosure := by
    rw [adjointGraph_topologicalClosure]; exact hcl hq
  exact hq' p hp

/-- The "basic criterion": a symmetric operator whose ranges under `T ± i` are dense
(here phrased as: nothing nonzero is orthogonal to them) is essentially self-adjoint. -/
