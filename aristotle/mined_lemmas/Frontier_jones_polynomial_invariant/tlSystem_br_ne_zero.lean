/-
# Jones Polynomial Invariant
Category: Frontier — Fields Medal Work
Target: Frontier.jones_polynomial_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Frontier

open LaurentPolynomial

/-! ## The coefficient ring

The Kauffman bracket takes values in the ring of Laurent polynomials `ℤ[A, A⁻¹]`,
which we realise as `LaurentPolynomial ℤ` with `A = T 1`. -/

/-- The coefficient ring `ℤ[A, A⁻¹]` of the Kauffman bracket. -/
abbrev KR : Type := LaurentPolynomial ℤ

/-- The variable `A`. -/

theorem tlSystem_br_ne_zero : tlSystem.br ≠ 0 := by
  intro h
  have h0 : tlSystem.br tlE = 0 := by rw [h]; rfl
  have h1 : tlSystem.br tlE = 1 := by simp [tlSystem, tlTr, tlE]
  rw [h1] at h0
  exact one_ne_zero h0

/-- The hypotheses of `Frontier.jones_polynomial_invariant` are consistent and not
vacuous: there are Kauffman systems with a nonzero bracket containing
Reidemeister I configurations, and Kauffman systems with a nonzero bracket
containing Reidemeister II and III configurations. -/
