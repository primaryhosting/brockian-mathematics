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
Essential self-adjointness via the basic criterion on deficiency subspaces.

This file develops, for an unbounded (partially defined) operator on a complex Hilbert
space, the classical criterion of von Neumann/Weyl:

  a densely defined symmetric operator `T` is essentially self-adjoint as soon as the two
  deficiency subspaces `ker (T† - i)` and `ker (T† + i)` are trivial.

Along the way we show that under this hypothesis the closure of `T` coincides with the
adjoint `T†`.
-/
import Mathlib

namespace Brockian.Weyl

open LinearPMap Complex
open scoped ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- An unbounded operator on a Hilbert space is *essentially self-adjoint* if its closure is
self-adjoint. -/

theorem closure_eq_adjoint_of_deficiency (hd : Dense (T.domain : Set H)) (hs : T.IsFormalAdjoint T)
    (h₁ : deficiency T I) (h₂ : deficiency T (-I)) :
    T.closure = T† := by
  have hle : T ≤ T† := le_adjoint_of_isSymmetric hd hs
  have hclosable : T.IsClosable :=
    isClosable_iff_exists_closed_extension.2 ⟨T†, adjoint_isClosed hd, hle⟩
  apply eq_of_eq_graph
  rw [← hclosable.graph_closure_eq_closure_graph]
  refine le_antisymm ?_ (adjoint_graph_le_graphClosure hd hs h₁ h₂)
  exact Submodule.topologicalClosure_minimal _ (le_graph_of_le hle) (adjoint_isClosed hd)

