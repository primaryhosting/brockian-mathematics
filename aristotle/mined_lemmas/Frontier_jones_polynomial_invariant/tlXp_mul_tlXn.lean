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

lemma tlXp_mul_tlXn : tlMul tlXp tlXn = ((1 : KR), (0 : KR)) := by
  have h1 : (T 1 : KR) * T (-1) = 1 := by rw [T_mul_T]; norm_num
  have h2 : (T 1 : KR) * T 1 = T 2 := by rw [T_mul_T]; norm_num
  have h3 : (T (-1) : KR) * T (-1) = T (-2) := by rw [T_mul_T]; norm_num
  have h4 : (T (-1) : KR) * T 1 = 1 := by rw [T_mul_T]; norm_num
  have hkey : (T 2 : KR) + T (-2) + loopValue = 0 := R2_cancel
  simp only [tlMul, tlXp, tlXn, Prod.mk.injEq]
  refine ⟨h1, ?_⟩
  rw [h2, h3, h4, mul_one]
  exact hkey

/-- The Reidemeister II identity in `TL₂`: the two crossings cancel. -/
