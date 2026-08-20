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

theorem adjoint_graph_le_graphClosure (hd : Dense (T.domain : Set H)) (hs : T.IsFormalAdjoint T)
    (h₁ : deficiency T I) (h₂ : deficiency T (-I)) :
    T†.graph ≤ T.graph.topologicalClosure := by
  rintro ⟨u, w⟩ huw
  obtain ⟨y, hy, hy'⟩ := T†.mem_graph_iff.1 huw
  simp only at hy hy'
  subst hy
  subst hy'
  obtain ⟨p, hp, hpz⟩ := exists_mem_graphClosure hd hs h₂ (T† y - I • (y : H))
  have hpmem : p ∈ T†.graph :=
    (Submodule.topologicalClosure_minimal _ (le_graph_of_le (le_adjoint_of_isSymmetric hd hs))
      (adjoint_isClosed hd)) hp
  obtain ⟨x, hx, hx'⟩ := T†.mem_graph_iff.1 hpmem
  have hvd : ((y : H) - (x : H)) ∈ T†.domain := T†.domain.sub_mem y.2 x.2
  have hkey : T† ⟨(y : H) - (x : H), hvd⟩ = I • ((y : H) - (x : H)) := by
    have hsub : (⟨(y : H) - (x : H), hvd⟩ : T†.domain) = y - x := rfl
    rw [hsub, LinearPMap.map_sub]
    have : T† y - T† x = I • (y : H) - I • (x : H) := by
      have := hpz
      rw [← hx, ← hx'] at this
      linear_combination (norm := module) -this
    rw [this, smul_sub]
  have hzero := h₁ ⟨(y : H) - (x : H), hvd⟩ hkey
  have hyx : y = x := Subtype.ext (sub_eq_zero.1 hzero)
  have hpe : ((x : H), (T† x : H)) = p := Prod.ext hx hx'
  rw [hyx, hpe]
  exact hp

/-- **Basic criterion of essential self-adjointness.** A densely defined symmetric operator with
trivial deficiency subspaces is essentially self-adjoint, and its closure is its adjoint. -/
