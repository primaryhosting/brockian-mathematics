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

noncomputable def tlR2 (p s : TL2) : R2Move tlSystem where
  top := (p, tlMul tlXn s)
  botA := (p, s)
  botB := (tlMul p tlE, s)
  base := tlMul p s
  cap := tlMul (tlMul p tlE) s
  h_top_A := (tlMul_assoc p tlXn s).symm
  h_top_B := (tlMul_assoc (tlMul p tlE) tlXn s).symm
  h_botA_A := rfl
  h_botA_B := rfl
  h_botB_A := rfl
  h_botB_B := by
    cases p; cases s
    simp only [tlSystem, tlMul, tlE, Prod.mk.injEq]
    constructor <;> ring
  wr_eq := rfl

/-- The Temperley–Lieb model also contains Reidemeister III configurations. -/
