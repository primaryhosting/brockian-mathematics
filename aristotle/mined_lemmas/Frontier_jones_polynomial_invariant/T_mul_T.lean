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

/-!
## Overview

We formalise the algebraic core of the statement "the Jones polynomial is a link
invariant": the Kauffman-bracket state sum, normalised by the writhe correction
factor `(-A^3)^{-w}`, is unchanged by the Reidemeister moves.

The coefficient ring is the ring of Laurent polynomials `ℤ[A, A⁻¹]`, realised as
`LaurentPolynomial ℤ` with `A = T 1`.

A knot/link diagram is abstracted by the two pieces of data that the Kauffman
construction actually uses: its writhe and its bracket polynomial (`BracketData`).
The Reidemeister moves are encoded through the skein-theoretic effect they have on
this data:

* `R1pos` / `R1neg`: a positive (resp. negative) kink changes the writhe by `±1`
  and replaces the bracket `b` by `A·(δ·b) + A⁻¹·b` (resp. `A⁻¹·(δ·b) + A·b`),
  where `δ = -A² - A⁻²` is the value of a disjoint unknotted circle.
* `R2`: resolving the two crossings of a Reidemeister-II tangle produces
  `(A² + δ + A⁻²)·h + v`, where `v` is the bracket of the untangled ("vertical")
  diagram and `h` that of the "horizontal" smoothing; the writhe is unchanged.
* `R3`: neither the writhe nor the bracket changes (this is the standard
  consequence of invariance under `R2`).

The two genuinely computational facts are then:

* `kauffman_kink_pos` / `kauffman_kink_neg` : `A·(δ·b) + A⁻¹·b = (-A³)·b` and
  `A⁻¹·(δ·b) + A·b = (-A⁻³)·b`;
* `kauffman_R2_coeff` : `A² + δ + A⁻² = 0`.

Combined with the writhe normalisation they give the main theorem
`Frontier.jones_polynomial_invariant`.
-/

namespace Frontier

open LaurentPolynomial

/-- The coefficient ring `ℤ[A, A⁻¹]` of the Kauffman bracket. -/
abbrev Lau := LaurentPolynomial ℤ

/-- The Kauffman variable `A`. -/

lemma T_mul_T (m n : ℤ) : (T m : Lau) * T n = T (m + n) := (T_add m n).symm

/-- The Kauffman kink factor `-A³`, as a unit of `ℤ[A, A⁻¹]`. -/
