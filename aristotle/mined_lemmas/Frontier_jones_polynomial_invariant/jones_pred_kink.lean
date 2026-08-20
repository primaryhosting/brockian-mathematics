import Mathlib

/-!
# Jones Polynomial Invariant
Category: Frontier — Fields Medal Work
Target: Frontier.jones_polynomial_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
## Overview

We formalise the skein-theoretic heart of Jones' theorem: the normalised Kauffman
bracket

  V(L) = (-A^3)^(-w(L)) * ⟨L⟩

is unchanged by the three Reidemeister moves.

Diagrams are kept abstract: they form an arbitrary type `D` equipped with a
bracket `br : D → ℤ[A, A⁻¹]`, an operation `addCircle` adding a disjoint
unknotted circle, and the circle axiom `⟨D ⊔ ○⟩ = δ ⟨D⟩` with
`δ = -A² - A⁻²`.  The Kauffman skein relation

  ⟨crossing⟩ = A ⟨A-smoothing⟩ + A⁻¹ ⟨B-smoothing⟩

enters as an explicit hypothesis at each crossing that a given Reidemeister
move touches; this is exactly the local data a link diagram provides.  From
these hypotheses we *derive* the classical consequences:

* R1 changes the bracket by the factor `-A^±3` (and hence leaves `V` invariant,
  since the writhe changes by `∓1`);
* R2 leaves the bracket unchanged;
* R3 leaves the bracket unchanged (its `B`-smoothings are compared using the
  R2 computation).

All the polynomial arithmetic takes place in the Laurent polynomial ring
`ℤ[A, A⁻¹] = LaurentPolynomial ℤ`, with `A = T 1`.
-/


namespace Frontier

open LaurentPolynomial

/-- The coefficient ring `ℤ[A, A⁻¹]` of the Kauffman bracket. -/
abbrev KL : Type := LaurentPolynomial ℤ

/-- The Kauffman variable `A`. -/

lemma jones_pred_kink (w : ℤ) (b : KL) :
    jones (w - 1) ((-T (-3) : KL) * b) = jones w b := by
  have : ((-T (-3) : KL)) = ((kinkUnit⁻¹ : KLˣ) : KL) := rfl
  rw [jones, jones, this, zpow_sub_one, ← mul_assoc]
  norm_cast
  rw [mul_assoc, inv_mul_cancel, mul_one]

/-!
### Main theorem
-/

/-- **The Jones polynomial is a link invariant.**

For any Kauffman bracket on an abstract type of link diagrams, the normalised
bracket `V(L) = (-A³)^{-w(L)} ⟨L⟩` is invariant under all three Reidemeister
moves:

1. a positive kink (R1) multiplies the bracket by `-A³` and the writhe by `+1`,
   and the two changes cancel;
2. a negative kink (R1) multiplies the bracket by `-A⁻³` and the writhe by `-1`,
   and again the changes cancel;
3. an R2 move leaves both the bracket and the writhe unchanged;
4. an R3 move leaves both the bracket and the writhe unchanged.

In each clause the hypotheses are the instances of the Kauffman skein relation
`⟨crossing⟩ = A ⟨A-smoothing⟩ + A⁻¹ ⟨B-smoothing⟩` at the crossings involved in
the move. -/
