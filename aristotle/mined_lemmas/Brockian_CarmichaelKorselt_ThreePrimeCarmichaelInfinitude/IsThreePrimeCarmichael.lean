import Mathlib

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

/-
# Three Prime Carmichael Infinitude
Category: Brockian Conjecture
Target: Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.CarmichaelKorselt

/-- Korselt's criterion, used here as the definition of a Carmichael number:
`n` is composite (`1 < n` and not prime), squarefree, and `p - 1 ∣ n - 1`
for every prime `p` dividing `n`. -/

def IsThreePrimeCarmichael (n : ℕ) : Prop :=
  IsCarmichael n ∧ ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p < q ∧ q < r ∧ n = p * q * r

/-- Korselt's criterion implies the Fermat property: a Carmichael number `n` in the above
sense satisfies `a ^ n ≡ a [MOD n]` for every base `a`.  This justifies the definition. -/
