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

noncomputable def tlR3 (p s : TL2) : R3Move tlSystem where
  left := (p, s)
  right := (p, s)
  hA := rfl
  r2left := tlR2 (tlMul p tlE) s
  r2right := tlR2 (tlMul p tlE) s
  hleft := tlMul_Xp_Xn (tlMul p tlE) s
  hright := tlMul_Xp_Xn (tlMul p tlE) s
  hbase := rfl
  wr_eq := rfl

/-- The bracket of the Temperley–Lieb model is nontrivial. -/
