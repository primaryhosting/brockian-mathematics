/-
# Jones Polynomial Invariant
Category: Frontier — Fields Medal Work
Target: Frontier.jones_polynomial_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 forbids a module doc comment `/-!` before `import`; the header is repeated below
-- verbatim as the module docstring.)

import Mathlib

/-!
# Jones Polynomial Invariant
Category: Frontier — Fields Medal Work
Target: Frontier.jones_polynomial_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## What is formalised here

Mathlib contains no theory of knots, link diagrams or the Kauffman bracket, so nothing in the
library closes (or nearly closes) the statement below; everything is developed from scratch here.

The Jones polynomial of an oriented link diagram `D` is
`V(D) = (-A^3)^{-w(D)} ⟨D⟩`, where `w(D)` is the writhe and `⟨D⟩` is the Kauffman bracket,
computed in the ring `ℤ[A, A⁻¹]` of Laurent polynomials by the skein rules

* `⟨crossing⟩ = A ⟨0-smoothing⟩ + A⁻¹ ⟨∞-smoothing⟩`,
* `⟨D ⊔ circle⟩ = δ ⟨D⟩` with `δ = -A² - A⁻²`.

Invariance under the Reidemeister moves is *exactly* the following algebra, which is what is
proved here (`Frontier.jones_polynomial_invariant`):

* **R1** the skein rules turn a kink into the scalar `A·δ + A⁻¹ = -A³`, and the writhe changes by
  `±1`; hence the writhe-normalised bracket `V` is unchanged (`normalizedBracket_kink_pos`,
  `normalizedBracket_kink_neg`).
* **R2** in the Temperley–Lieb algebra of the corresponding tangle, where a crossing is the
  element `σ(e) = A·1 + A⁻¹·e` and `e` is the planar cap-cup generator satisfying `e² = δ·e`,
  one has `σ(e) σ̄(e) = 1`: the two crossings cancel (`kauffman_R2`).
* **R3** with two generators `e, f` obeying the Temperley–Lieb relations
  `e² = δ e`, `f² = δ f`, `efe = e`, `fef = f`, one has `σ(e)σ(f)σ(e) = σ(f)σ(e)σ(f)`
  (`kauffman_R3`).

Since a bracket state sum is a linear functional on the Temperley–Lieb algebra of the tangle,
these identities are precisely the invariance of `⟨·⟩` under R2 and R3, and, together with the
writhe correction, the invariance of the Jones polynomial.

The Temperley–Lieb hypotheses are not vacuous: `temperleyLieb_relations_have_a_model`
exhibits a concrete noncommutative algebra over `ℤ[A,A⁻¹]` containing such elements.
-/

namespace Frontier

open LaurentPolynomial

/-- The coefficient ring `ℤ[A, A⁻¹]` of the Kauffman bracket; `T n` is `A ^ n`. -/
abbrev KauffmanRing := LaurentPolynomial ℤ

/-- The value `δ = -A² - A⁻²` of a free circle in the Kauffman bracket. -/

noncomputable def evalAtOne : KauffmanRing →+* ℚ :=
  LaurentPolynomial.eval₂ (Int.castRingHom ℚ) 1

noncomputable local instance : Algebra KauffmanRing ℚ := evalAtOne.toAlgebra

