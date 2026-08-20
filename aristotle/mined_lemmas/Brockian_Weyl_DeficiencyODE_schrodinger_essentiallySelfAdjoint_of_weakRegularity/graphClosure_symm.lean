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

theorem graphClosure_symm (hs : T.IsFormalAdjoint T) {p q : H × H}
    (hp : p ∈ T.graph.topologicalClosure) (hq : q ∈ T.graph.topologicalClosure) :
    ⟪p.2, q.1⟫ = ⟪p.1, q.2⟫ := by
  -- first fix `q` in the graph and let `p` vary
  have step1 : ∀ p' ∈ T.graph.topologicalClosure, ∀ q' ∈ T.graph,
      ⟪p'.2, q'.1⟫ = ⟪p'.1, q'.2⟫ := by
    intro p' hp' q' hq'
    have hclosed : IsClosed {r : H × H | ⟪r.2, q'.1⟫ = ⟪r.1, q'.2⟫} := by
      have : Continuous fun r : H × H => ⟪r.2, q'.1⟫ - ⟪r.1, q'.2⟫ := by fun_prop
      simpa [Set.ext_iff, sub_eq_zero] using isClosed_eq (by fun_prop :
        Continuous fun r : H × H => ⟪r.2, q'.1⟫) (by fun_prop :
        Continuous fun r : H × H => ⟪r.1, q'.2⟫)
    have hsub : (T.graph : Set (H × H)) ⊆ {r : H × H | ⟪r.2, q'.1⟫ = ⟪r.1, q'.2⟫} := by
      rintro r hr
      obtain ⟨a, ha, ha'⟩ := T.mem_graph_iff.1 hr
      obtain ⟨b, hb, hb'⟩ := T.mem_graph_iff.1 hq'
      simp only [Set.mem_setOf_eq, ← ha, ← ha', ← hb, ← hb']
      exact hs a b
    have : (T.graph.topologicalClosure : Set (H × H)) ⊆
        {r : H × H | ⟪r.2, q'.1⟫ = ⟪r.1, q'.2⟫} := by
      rw [Submodule.topologicalClosure_coe]
      exact hclosed.closure_subset_iff.2 hsub
    exact this hp'
  -- now fix `p` in the closure and let `q` vary
  have hclosed : IsClosed {r : H × H | ⟪p.2, r.1⟫ = ⟪p.1, r.2⟫} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  have hsub : (T.graph : Set (H × H)) ⊆ {r : H × H | ⟪p.2, r.1⟫ = ⟪p.1, r.2⟫} := by
    intro r hr
    exact step1 p hp r hr
  have : (T.graph.topologicalClosure : Set (H × H)) ⊆
      {r : H × H | ⟪p.2, r.1⟫ = ⟪p.1, r.2⟫} := by
    rw [Submodule.topologicalClosure_coe]
    exact hclosed.closure_subset_iff.2 hsub
  exact this hq

omit [CompleteSpace H] in
/-- For a point `(x, y)` in the closure of the graph of a symmetric operator we have
`‖y - i • x‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2`. -/
