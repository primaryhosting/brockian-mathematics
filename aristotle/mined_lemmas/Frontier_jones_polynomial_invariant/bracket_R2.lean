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

theorem bracket_R2 (K : KauffmanBracket D) (d2 eA eB cupcap idt : D)
    (h1 : K.br d2 = Avar * K.br eA + Ainv * K.br eB)
    (h2 : K.br eA = Avar * K.br cupcap + Ainv * K.br idt)
    (h3 : K.br eB = Avar * K.br (K.addCircle cupcap) + Ainv * K.br cupcap) :
    K.br d2 = K.br idt := by
  rw [h1, h2, h3, K.br_addCircle]
  linear_combination (K.br cupcap) * sq_add_delta_add_invSq
    + (delta * K.br cupcap + K.br idt) * Avar_mul_Ainv

/-!
### Reidemeister move III
-/

/-- **R3.**  Resolve the crossing that moves across the third strand in both
diagrams.  The `A`-resolutions `aL`, `aR` agree by planar isotopy, while the
`B`-resolutions `bL`, `bR` are each simplified by an R2 move to a common
diagram (with resolution data `_L`/`_R`).  Hence the brackets agree. -/
