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

import Mathlib

/-!
# Three Prime Carmichael Infinitude
Category: Brockian Conjecture
Target: Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.CarmichaelKorselt

/-- A Carmichael number: a composite `n > 1` such that Fermat's little theorem
congruence `a ^ (n - 1) ≡ 1 [MOD n]` holds for every `a` coprime to `n`. -/

def ChernickDicksonHypothesis : Prop :=
  ∀ N : ℕ, ∃ k, N < k ∧ Nat.Prime (6 * k + 1) ∧ Nat.Prime (12 * k + 1) ∧
    Nat.Prime (18 * k + 1)

/-- Local Korselt step: if `p` is prime and `p - 1 ∣ n - 1` (with `n ≥ 1`), then
`a ^ n ≡ a [MOD p]` for every `a`. -/
