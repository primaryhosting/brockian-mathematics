/-
# Modularity
Category: Frontier Math
Target: Math2.modularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math2

/-!
## Point counts on integral Weierstrass models

For a Weierstrass curve `W` over `ℤ` and a prime `p`, `affineCount W p` counts the pairs
`(x, y) ∈ {0, …, p-1}²` satisfying the Weierstrass equation modulo `p`, i.e. the affine
`𝔽_p`-points of the reduction of `W`.  The projective curve has exactly one further point,
the point at infinity `[0 : 1 : 0]`, so the number of `𝔽_p`-points of the reduction is
`affineCount W p + 1`, and the trace of Frobenius is
`a_p = p + 1 - (affineCount W p + 1) = p - affineCount W p`.
-/

/-- The number of affine solutions of the Weierstrass equation of `W` over `𝔽_p`,
computed with representatives `0, …, p-1`. -/

def apOf (W : WeierstrassCurve ℤ) (p : ℕ) : ℤ := (p : ℤ) - (affineCount W p : ℤ)

/-!
## The modularity statement

`ModularityStatement` records the Taniyama–Shimura–Wiles theorem in the following shape:
for every elliptic curve over `ℚ`, presented by an integral Weierstrass model `W` with
non-vanishing discriminant, there is a level `N ≥ 1` and a normalised weight-`2` cusp form `f`
on `Γ₀(N)` whose `q`-expansion coefficients at all primes of good reduction for `W` are the
traces of Frobenius `a_p` of `W`.

This is a `Prop`-valued *definition*: it records the statement, it is not asserted here.
-/

/-- Formal statement of the modularity theorem for elliptic curves over `ℚ`: every integral
Weierstrass model with nonzero discriminant has its Frobenius traces matched by the
`q`-expansion coefficients of a normalised weight-two cusp form on some `Γ₀(N)`. -/
