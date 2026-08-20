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

noncomputable def circlesBracket : KauffmanBracket ℕ where
  br n := delta ^ n
  addCircle := Nat.succ
  br_addCircle n := by rw [pow_succ]; ring

/-!
### Reidemeister move I
-/

/-- **R1, positive kink.**  If `dk` is obtained from `strand` by adding a kink
whose `A`-smoothing splits off a circle and whose `B`-smoothing undoes the
kink, then `⟨dk⟩ = -A³ ⟨strand⟩`. -/
