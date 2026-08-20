import Mathlib

/-!
# Jones Polynomial Invariant
Category: Frontier — Fields Medal Work
Target: Frontier.jones_polynomial_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

open LaurentPolynomial

/-! ## The coefficient ring of the Kauffman bracket -/

/-- The coefficient ring `ℤ[A, A⁻¹]` of the Kauffman bracket. -/
abbrev KRing : Type := LaurentPolynomial ℤ

/-- The Kauffman variable `A`. -/

theorem delta_relation : A * A + Ainv * Ainv + delta = 0 := by
  rw [A_sq, Ainv_sq, delta]; ring

/-! ## Kauffman's skein relation and the Reidemeister I coefficients

Resolving a kink with the skein relation
`⟨crossing⟩ = A ⟨0-smoothing⟩ + A⁻¹ ⟨∞-smoothing⟩`
reproduces the diagram once and the diagram with an extra free loop (a factor `δ`)
once.  The resulting overall coefficients are computed here. -/

/-- Reidemeister I with a positive kink multiplies the Kauffman bracket by `-A³`. -/
