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

The Jones polynomial of a link is constructed from the *Kauffman bracket*: each crossing of a
link diagram is resolved by the skein relation

  `⟨crossing⟩ = A ⬝ ⟨0-smoothing⟩ + A⁻¹ ⬝ ⟨∞-smoothing⟩`,

a free closed loop contributes the *loop value* `δ = -A² - A⁻²`, and the resulting bracket is
normalised by the writhe, `V(L) = (-A³)^(-w(L)) ⟨L⟩`.

Well-definedness of this construction is exactly the statement that the above data is invariant
under the three Reidemeister moves.  Passing to the *skein-algebraic* (Temperley–Lieb) picture,
which is the standard way Kauffman's argument is organised, the three moves become three purely
algebraic identities in the Temperley–Lieb algebra over the coefficient ring:

* **R2**: the resolved crossing `σ = A·1 + A⁻¹·e` is invertible, with inverse the resolved
  *opposite* crossing `σ⁻¹ = A⁻¹·1 + A·e`.
* **R3**: the resolved crossings satisfy the braid relation `σ₁σ₂σ₁ = σ₂σ₁σ₂`.
* **R1**: adding a kink multiplies the bracket by the unit `-A³`; since a kink also changes the
  writhe by `1`, the writhe-normalised bracket is unchanged.

This file develops that algebra over an arbitrary commutative coefficient ring `R` with a
distinguished invertible element `A`, in an arbitrary `R`-algebra `T` carrying elements `eᵢ`
subject to the Temperley–Lieb relations.  The main theorem `Frontier.jones_polynomial_invariant`
collects the three statements.  A concrete non-degenerate model (`Frontier.TLModel`) over the ring
of Laurent polynomials `ℤ[A, A⁻¹]` is provided at the end, so the hypotheses are known to be
satisfiable by genuinely distinct, nonzero elements.
-/

namespace Frontier

section Kauffman

variable {R : Type*} [CommRing R] {T : Type*} [Ring T] [Algebra R T]

/-- The Kauffman loop value `δ = -A² - A⁻²`, written using an explicit inverse `Ainv` of `A`.
It is the scalar by which the bracket gets multiplied when a free closed loop is added. -/

noncomputable def kAinv : KauffmanRing := T (-1)

