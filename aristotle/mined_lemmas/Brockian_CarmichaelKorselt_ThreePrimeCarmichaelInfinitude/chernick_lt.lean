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

/-- A *Carmichael number*: a composite `n > 1` such that `a ^ (n - 1) ≡ 1 [MOD n]` for every
`a` coprime to `n` (i.e. a Fermat pseudoprime to every admissible base). -/

theorem chernick_lt {k : ℕ} (hk : 0 < k) : 6 * k + 1 < 12 * k + 1 ∧ 12 * k + 1 < 18 * k + 1 := by
  omega

/-- **Chernick's construction.** If `6k+1`, `12k+1`, `18k+1` are all prime (with `k ≥ 1`), then
their product is a Carmichael number with exactly three prime factors. -/
