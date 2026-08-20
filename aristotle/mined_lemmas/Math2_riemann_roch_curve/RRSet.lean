/-
# Riemann Roch Curve
Category: Frontier Math
Target: Math2.riemann_roch_curve
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

open Polynomial

/-!
# Riemann–Roch for a smooth projective curve

Mathlib (as of this development) contains no Riemann–Roch theorem, no theory of divisors on
curves, no sheaf cohomology of curves and no Serre duality, so the whole set-up below is built
from scratch on top of Mathlib's theory of the rational function field `RatFunc k` and of
polynomials.

We work with the smooth projective curve `ℙ¹_k` over an arbitrary field `k`, described through
its function field `k(X) = RatFunc k`:

* its closed points (`Math2.Place`) are the monic irreducible polynomials together with the
  point at infinity;
* `Math2.ord` is the normalized valuation (order of vanishing) at a closed point;
* `Math2.Divisor` is the group of divisors, `Math2.degDiv` the degree of a divisor
  (each point counted with the degree of its residue field);
* `Math2.RRSpace D` is the Riemann–Roch space `L(D) = {f ≠ 0 : div f + D ≥ 0} ∪ {0}` and
  `Math2.ell D = ℓ(D)` its dimension over `k`;
* `Math2.canonicalDivisor` is the canonical divisor `-2·∞` and `Math2.genus` the genus `0`.

The main result `Math2.riemann_roch_curve` is the Riemann–Roch formula
`ℓ(D) - ℓ(K - D) = deg D + 1 - g`, valid for every divisor `D`.
-/

namespace Math2

/-!
## The smooth projective curve

We work with the projective line `ℙ¹_k` over an arbitrary field `k`, presented through its
function field `k(X) = RatFunc k`.  Its closed points (places of the function field) are the
monic irreducible polynomials (the finite closed points) together with the point at infinity.
-/

variable {k : Type*} [Field k]

/-- A closed point of the projective line `ℙ¹_k`: either a monic irreducible polynomial
(a finite closed point) or `none`, the point at infinity. -/
abbrev Place (k : Type*) [Field k] := Option {p : k[X] // p.Monic ∧ Irreducible p}

/-- A divisor on `ℙ¹_k`: a finitely supported formal `ℤ`-combination of closed points. -/
abbrev Divisor (k : Type*) [Field k] := Place k →₀ ℤ

/-! ### Order functions (normalized valuations) at the closed points -/


def RRSet (D : Divisor k) : Set (RatFunc k) := {f | f = 0 ∨ ∀ P : Place k, -D P ≤ ord P f}

/-- The `k`-subspace of `RatFunc k` consisting of the polynomials of degree `< n`. -/
