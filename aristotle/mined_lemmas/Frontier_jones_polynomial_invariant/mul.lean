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

set_option autoImplicit false

namespace Frontier

/-!
## The Kauffman-bracket model of the Jones polynomial

The Jones polynomial of a link is obtained from the Kauffman bracket state sum
of a link diagram, normalised by the writhe.  The content of the statement
"the Jones polynomial is a link invariant" is the invariance of this
construction under the three Reidemeister moves, and this is a purely local,
algebraic computation in the Temperley–Lieb algebras over the coefficient ring,
where a crossing is resolved as

    ⟨crossing⟩ = A · ⟨identity smoothing⟩ + A⁻¹ · ⟨cup–cap smoothing⟩

and a closed loop contributes the factor `d = -A² - A⁻²`.

This file sets up the Temperley–Lieb algebras `TL₂` and `TL₃` over an arbitrary
commutative ring (with loop parameter `d`), defines the Kauffman resolution of
a crossing, and proves the three local invariance statements:

* Reidemeister I : a kink multiplies the bracket by `-A³`, so the writhe
  normalisation `(-A³)^(-w) ⟨D⟩` is unchanged;
* Reidemeister II: `σ⁺ · σ⁻ = 1` in `TL₂`;
* Reidemeister III: `σ₁ σ₂ σ₁ = σ₂ σ₁ σ₂` in `TL₃`.
-/

namespace Jones

/-! ### The Temperley–Lieb algebra `TL₂`

Basis: the identity diagram `1` and the cup–cap diagram `e`, with `e * e = d * e`.
-/

/-- An element of the Temperley–Lieb algebra on two strands, written in the
planar basis `{1, e}`. -/
structure TL2 (K : Type*) where
  /-- coefficient of the identity diagram -/
  c1 : K
  /-- coefficient of the cup–cap diagram `e` -/
  ce : K

namespace TL2

variable {K : Type*} [CommRing K]

omit [CommRing K] in

def mul (d : K) (x y : TL3 K) : TL3 K :=
  ⟨ x.c1 * y.c1,
    x.c1 * y.ca + x.ca * y.c1 + d * x.ca * y.ca + x.ca * y.cba + x.cab * y.ca
      + d * x.cab * y.cba,
    x.c1 * y.cb + x.cb * y.c1 + d * x.cb * y.cb + x.cb * y.cab + x.cba * y.cb
      + d * x.cba * y.cab,
    x.c1 * y.cab + x.ca * y.cb + d * x.ca * y.cab + x.cab * y.c1
      + d * x.cab * y.cb + x.cab * y.cab,
    x.c1 * y.cba + x.cb * y.ca + d * x.cb * y.cba + x.cba * y.c1
      + d * x.cba * y.ca + x.cba * y.cba ⟩

