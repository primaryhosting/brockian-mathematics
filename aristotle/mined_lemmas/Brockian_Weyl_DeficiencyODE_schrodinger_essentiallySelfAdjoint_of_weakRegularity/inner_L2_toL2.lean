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

theorem inner_L2_toL2 (v : L2R) (g : 𝓢(ℝ, ℂ)) :
    ⟪v, toL2 g⟫ = ∫ x, conj ((v : ℝ → ℂ) x) * g x := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_toL2 g] with x h2
  rw [h2, RCLike.inner_apply]
  ring

/-- **Weak regularity.**  If `u, w ∈ L²(ℝ)` and `w = -u''` in the sense of distributions
(tested against Schwartz functions), then `⟪u, w⟫` is real.  On the Fourier side this is the
fact that `ŵ = (2πξ)² û`, so that `⟪u, w⟫ = ∫ (2πξ)² |û|²`. -/
