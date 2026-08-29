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

noncomputable def twistSystem : KauffmanSystem where
  D := ℕ × ℤ
  Site := ℕ × ℤ
  br := fun p => loopValue ^ p.1 * ((kinkUnit ^ p.2 : KRˣ) : KR)
  wr := fun p => p.2
  addCircle := fun p => (p.1 + 1, p.2)
  pos := fun p => (p.1, p.2 + 1)
  neg := fun p => (p.1, p.2 - 1)
  sA := fun p => (p.1 + 1, p.2)
  sB := fun p => p
  br_addCircle := by
    rintro ⟨k, w⟩
    simp only [pow_succ]
    ring
  wr_addCircle := by rintro ⟨k, w⟩; rfl
  br_pos := by
    rintro ⟨k, w⟩
    simp only [kinkUnit_zpow_succ, pow_succ]
    linear_combination (-(loopValue ^ k * ((kinkUnit ^ w : KRˣ) : KR))) * kinkA
  br_neg := by
    rintro ⟨k, w⟩
    simp only [kinkUnit_zpow_pred, pow_succ]
    linear_combination (-(loopValue ^ k * ((kinkUnit ^ w : KRˣ) : KR))) * kinkB

/-- Every crossing of the model is a Reidemeister I kink. -/
