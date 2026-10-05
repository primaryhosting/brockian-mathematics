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

noncomputable def tlSystem : KauffmanSystem where
  D := TL2
  Site := TL2 × TL2
  br := tlTr
  wr := fun _ => 0
  addCircle := fun x => (loopValue * x.1, loopValue * x.2)
  pos := fun s => tlMul (tlMul s.1 tlXp) s.2
  neg := fun s => tlMul (tlMul s.1 tlXn) s.2
  sA := fun s => tlMul s.1 s.2
  sB := fun s => tlMul (tlMul s.1 tlE) s.2
  br_addCircle := by rintro ⟨a, b⟩; simp only [tlTr]; ring
  wr_addCircle := by rintro ⟨a, b⟩; rfl
  br_pos := by
    rintro ⟨⟨p1, p2⟩, ⟨s1, s2⟩⟩
    simp only [tlMul, tlTr, tlXp, tlE]
    ring
  br_neg := by
    rintro ⟨⟨p1, p2⟩, ⟨s1, s2⟩⟩
    simp only [tlMul, tlTr, tlXn, tlE]
    ring

/-- Every pair of `TL₂` elements gives a Reidemeister II configuration in the
Temperley–Lieb model. -/
