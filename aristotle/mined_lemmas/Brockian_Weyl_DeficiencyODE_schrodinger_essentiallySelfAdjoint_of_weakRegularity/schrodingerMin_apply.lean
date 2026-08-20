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

theorem schrodingerMin_apply (hV : BoundedPotential V C volume) (f : 𝓢(ℝ, ℂ))
    (hf : (toL2 f : L2R) ∈ (schrodingerMin hV).domain) :
    schrodingerMin hV ⟨toL2 f, hf⟩ = schrodingerAux hV f := by
  have hsymm : (LinearEquiv.ofInjective (toL2 : 𝓢(ℝ, ℂ) →ₗ[ℂ] L2R) toL2_injective).symm
      ⟨toL2 f, hf⟩ = f := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  show schrodingerAux hV ((LinearEquiv.ofInjective _ toL2_injective).symm ⟨toL2 f, hf⟩) = _
  rw [hsymm]

