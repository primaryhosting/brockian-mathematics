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

def affineCount (W : WeierstrassCurve ℤ) (p : ℕ) : ℕ :=
  ((List.range p).flatMap fun x => (List.range p).map fun y => (x, y)).countP
    (fun q =>
      (((q.2 : ℤ) ^ 2 + W.a₁ * (q.1 : ℤ) * (q.2 : ℤ) + W.a₃ * (q.2 : ℤ))
        - ((q.1 : ℤ) ^ 3 + W.a₂ * (q.1 : ℤ) ^ 2 + W.a₄ * (q.1 : ℤ) + W.a₆)) % (p : ℤ) == 0)

/-- The trace of Frobenius `a_p = p + 1 - #E(𝔽_p)` of the reduction mod `p` of an integral
Weierstrass model (meaningful at primes of good reduction, i.e. `p ∤ Δ`). -/
