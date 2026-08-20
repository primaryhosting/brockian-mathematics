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

theorem BoundedPotential.inner_mul_self_isReal (hV : BoundedPotential V C μ) (f : Lp ℂ 2 μ) :
    conj (inner ℂ f (hV.mul f)) = inner ℂ f (hV.mul f) := by
  rw [L2.inner_def, ← integral_conj]
  refine integral_congr_ae ?_
  filter_upwards [hV.coeFn_mulₗ f] with x h1
  rw [BoundedPotential.mul_apply, h1]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal, Complex.conj_conj]
  ring

end Mul

end Brockian.Weyl

/-
# Essential self-adjointness of one-dimensional Schrödinger operators

We consider the Schrödinger operator `-d²/dx² + V` on the line, with a bounded measurable
real potential `V`, defined on the Schwartz space `𝓢(ℝ, ℂ)` viewed as a dense subspace of
`L²(ℝ)`.

The main result `schrodinger_essentiallySelfAdjoint_of_weakRegularity` states that this
operator is essentially self-adjoint.  The proof goes through the deficiency (Weyl) ODE:
an element `u` of the domain of the adjoint with `T† u = ± i u` is a weak (distributional)
solution of the deficiency equation `-u'' + V u = ± i u`.  The *weak regularity* input,
which is discharged here rather than assumed, is the statement that for a weak solution the
quantity `⟪u, -u''⟫` is real; on the Fourier side this is the identity
`⟪u, -u''⟫ = ∫ (2πξ)² |û(ξ)|² ∂ξ`.
-/
import Brockian.Weyl.Deficiency
import Brockian.Weyl.Multiplication

namespace Brockian.Weyl.DeficiencyODE

open MeasureTheory SchwartzMap FourierTransform Complex LinearPMap Brockian.Weyl
open scoped ComplexConjugate

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- The Hilbert space `L²(ℝ)`. -/
noncomputable abbrev L2R := Lp (α := ℝ) ℂ 2 volume

/-- A Schwartz function, viewed as an element of `L²(ℝ)`. -/
