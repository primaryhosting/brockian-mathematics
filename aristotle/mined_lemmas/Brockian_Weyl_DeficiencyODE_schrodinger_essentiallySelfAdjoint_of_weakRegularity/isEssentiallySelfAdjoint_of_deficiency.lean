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

theorem isEssentiallySelfAdjoint_of_deficiency (hd : Dense (T.domain : Set H))
    (hs : T.IsFormalAdjoint T) (h₁ : deficiency T I) (h₂ : deficiency T (-I)) :
    IsEssentiallySelfAdjoint T := by
  have hcl := closure_eq_adjoint_of_deficiency hd hs h₁ h₂
  -- the adjoint is symmetric, since its graph is the closure of the graph of `T`
  have hclosable : T.IsClosable :=
    isClosable_iff_exists_closed_extension.2
      ⟨T†, adjoint_isClosed hd, le_adjoint_of_isSymmetric hd hs⟩
  have hgraph : T†.graph = T.graph.topologicalClosure := by
    rw [← hcl, ← hclosable.graph_closure_eq_closure_graph]
  have hsymm : T†.IsFormalAdjoint T† := by
    intro x y
    have hx : ((x : H), T† x) ∈ T.graph.topologicalClosure := by
      rw [← hgraph]; exact T†.mem_graph x
    have hy : ((y : H), T† y) ∈ T.graph.topologicalClosure := by
      rw [← hgraph]; exact T†.mem_graph y
    exact graphClosure_symm hs hx hy
  have hd' : Dense (T†.domain : Set H) := by
    apply Dense.mono _ hd
    intro x hx
    exact (le_adjoint_of_isSymmetric hd hs).1 hx
  have hle1 : T† ≤ T†† := hsymm.le_adjoint hd'
  have hle2 : T†† ≤ T† := adjoint_le_adjoint_of_le hd (le_adjoint_of_isSymmetric hd hs) hd'
  rw [IsEssentiallySelfAdjoint, hcl, isSelfAdjoint_def]
  exact le_antisymm hle2 hle1

end Criterion

end Brockian.Weyl

/-
Multiplication by a bounded real function as a bounded self-adjoint operator on `L²`.
-/
import Mathlib

namespace Brockian.Weyl

open MeasureTheory Complex
open scoped ComplexConjugate

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

section Mul

/-- The hypotheses we require of the potential: it is measurable and bounded by `C`. -/
structure BoundedPotential (V : α → ℝ) (C : ℝ) (μ : Measure α) : Prop where
  measurable : AEStronglyMeasurable V μ
  le_bound : ∀ᵐ x ∂μ, |V x| ≤ C

variable {V : α → ℝ} {C : ℝ}

