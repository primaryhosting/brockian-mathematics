/-
# Quadratic Reciprocity
Category: Pure Mathematics
Target: Math.quadratic_reciprocity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Quadratic Reciprocity
Category: Pure Mathematics
Target: Math.quadratic_reciprocity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math

/-- **Law of quadratic reciprocity.**  For distinct odd primes `p` and `q`,
the product of the Legendre symbols `(p/q)` and `(q/p)` equals
`(-1) ^ (((p-1)/2) * ((q-1)/2))`. -/

theorem quadratic_reciprocity' (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : p ≠ q) :
    @legendreSym q ⟨hq⟩ p * @legendreSym p ⟨hp⟩ q
      = (-1) ^ ((p - 1) / 2 * ((q - 1) / 2)) :=
  @quadratic_reciprocity p q ⟨hp⟩ ⟨hq⟩ hp2 hq2 hpq

/-- Reciprocity in the case `p ≡ 3 [MOD 4]` and `q ≡ 3 [MOD 4]`: exactly one of `p`, `q` is a
quadratic residue modulo the other. -/
