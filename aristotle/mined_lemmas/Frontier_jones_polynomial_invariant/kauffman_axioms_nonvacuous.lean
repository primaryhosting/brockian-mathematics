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

theorem kauffman_axioms_nonvacuous :
    (∃ S : KauffmanSystem, S.br ≠ 0 ∧ Nonempty (R1Move S)) ∧
    (∃ S : KauffmanSystem, S.br ≠ 0 ∧ Nonempty (R2Move S) ∧ Nonempty (R3Move S)) :=
  ⟨⟨twistSystem, twistSystem_br_ne_zero, ⟨twistR1 0 0⟩⟩,
   ⟨tlSystem, tlSystem_br_ne_zero, ⟨tlR2 ((1 : KR), (0 : KR)) ((1 : KR), (0 : KR))⟩,
     ⟨tlR3 ((1 : KR), (0 : KR)) ((1 : KR), (0 : KR))⟩⟩⟩

end Frontier

