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

theorem inner_neg_D2_symm (f g : 𝓢(ℝ, ℂ)) :
    ⟪toL2 (-(D2 f)), toL2 g⟫ = ⟪toL2 f, toL2 (-(D2 g))⟫ := by
  have h1 : ⟪toL2 (-(D2 f)), toL2 g⟫ = ⟪𝓕 (toL2 (-(D2 f))), 𝓕 (toL2 g)⟫ :=
    (Lp.inner_fourier_eq _ _).symm
  have h2 : ⟪toL2 f, toL2 (-(D2 g))⟫ = ⟪𝓕 (toL2 f), 𝓕 (toL2 (-(D2 g)))⟫ :=
    (Lp.inner_fourier_eq _ _).symm
  rw [h1, h2, fourier_toL2, fourier_toL2, fourier_toL2, fourier_toL2, inner_toL2, inner_toL2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [fourier_neg_D2, fourier_neg_D2]
  simp only [map_mul, Complex.conj_ofReal]
  ring

