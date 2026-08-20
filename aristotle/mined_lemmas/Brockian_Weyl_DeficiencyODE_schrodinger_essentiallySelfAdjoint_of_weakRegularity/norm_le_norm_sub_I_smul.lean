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

theorem norm_le_norm_sub_I_smul (hs : T.IsFormalAdjoint T) {p : H × H}
    (hp : p ∈ T.graph.topologicalClosure) :
    ‖p‖ ≤ ‖p.2 - I • p.1‖ := by
  have h := norm_sub_I_smul_sq hs hp
  have h1 : ‖p.1‖ ^ 2 ≤ ‖p.2 - I • p.1‖ ^ 2 := by
    rw [h]; nlinarith [norm_nonneg p.2]
  have h2 : ‖p.2‖ ^ 2 ≤ ‖p.2 - I • p.1‖ ^ 2 := by
    rw [h]; nlinarith [norm_nonneg p.1]
  have h1' : ‖p.1‖ ≤ ‖p.2 - I • p.1‖ :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h1
  have h2' : ‖p.2‖ ≤ ‖p.2 - I • p.1‖ :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2
  rw [Prod.norm_def]
  exact max_le h1' h2'

/-- The `-i` deficiency condition implies that `y - i • x` runs through all of `H` as `(x, y)`
runs through the closure of the graph. -/
