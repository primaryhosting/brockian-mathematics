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

import Mathlib

/-!
# The basic criterion for essential self-adjointness

This file develops the abstract operator-theoretic input for `Brockian.Weyl.FreeLaplacian2`:
a densely defined symmetric operator on a complex Hilbert space whose two deficiency ranges
`Ran (T + i)` and `Ran (T - i)` are dense has self-adjoint closure, i.e. it is
*essentially self-adjoint*.
-/

namespace Brockian.Weyl

open LinearPMap Complex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The operator `x ↦ T x + z • x` on the domain of `T`. -/

theorem adjoint_closure_eq {T : H →ₗ.[ℂ] H} (hdom : Dense (T.domain : Set H))
    (hsymm : T.IsFormalAdjoint T) : (T.closure)† = T† := by
  have hcl : T.IsClosable := isClosable_of_isFormalAdjoint_self hdom hsymm
  apply LinearPMap.eq_of_eq_graph
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint (dense_domain_closure hdom),
    LinearPMap.adjoint_graph_eq_graph_adjoint hdom, ← hcl.graph_closure_eq_closure_graph,
    submodule_adjoint_topologicalClosure]

omit [CompleteSpace H] in
/-- For a symmetric operator and purely imaginary `z`,
`‖T x + z • x‖ ^ 2 = ‖T x‖ ^ 2 + ‖z‖ ^ 2 * ‖x‖ ^ 2`. -/
