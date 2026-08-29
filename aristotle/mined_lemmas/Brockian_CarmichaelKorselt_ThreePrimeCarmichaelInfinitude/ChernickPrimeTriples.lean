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

-- (The header above uses `/-` rather than `/-!` because Lean 4 does not permit a module
-- docstring to precede the `import` block; the text is otherwise verbatim.)

import Mathlib

/-!
# Three Prime Carmichael Infinitude
Category: Brockian Conjecture
Target: Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.CarmichaelKorselt

/-- `n` is a Carmichael number: it is composite, yet `a ^ n ≡ a [ZMOD n]` for every integer `a`. -/

def ChernickPrimeTriples : Prop :=
  ∀ N : ℕ, ∃ k > N, Nat.Prime (6 * k + 1) ∧ Nat.Prime (12 * k + 1) ∧ Nat.Prime (18 * k + 1)

/-- The Korselt step for a single prime: if `p` is prime, `n ≥ 1` and `(p-1) ∣ (n-1)`,
then `p ∣ a ^ n - a` for every integer `a`. -/
