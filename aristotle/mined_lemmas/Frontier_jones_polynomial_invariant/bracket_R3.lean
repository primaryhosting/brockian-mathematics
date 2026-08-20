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

theorem bracket_R3 (K : KauffmanBracket D)
    (dL dR aL aR bL bR eAL eBL eAR eBR cupcapL cupcapR common : D)
    (h1 : K.br dL = Avar * K.br aL + Ainv * K.br bL)
    (h2 : K.br dR = Avar * K.br aR + Ainv * K.br bR)
    (ha : K.br aL = K.br aR)
    (hbL1 : K.br bL = Avar * K.br eAL + Ainv * K.br eBL)
    (hbL2 : K.br eAL = Avar * K.br cupcapL + Ainv * K.br common)
    (hbL3 : K.br eBL = Avar * K.br (K.addCircle cupcapL) + Ainv * K.br cupcapL)
    (hbR1 : K.br bR = Avar * K.br eAR + Ainv * K.br eBR)
    (hbR2 : K.br eAR = Avar * K.br cupcapR + Ainv * K.br common)
    (hbR3 : K.br eBR = Avar * K.br (K.addCircle cupcapR) + Ainv * K.br cupcapR) :
    K.br dL = K.br dR := by
  have hL : K.br bL = K.br common := bracket_R2 K bL eAL eBL cupcapL common hbL1 hbL2 hbL3
  have hR : K.br bR = K.br common := bracket_R2 K bR eAR eBR cupcapR common hbR1 hbR2 hbR3
  rw [h1, h2, ha, hL, hR]

/-!
### The Jones normalisation
-/

/-- The unit `-A³` of `ℤ[A, A⁻¹]`, whose inverse is `-A⁻³`. -/
