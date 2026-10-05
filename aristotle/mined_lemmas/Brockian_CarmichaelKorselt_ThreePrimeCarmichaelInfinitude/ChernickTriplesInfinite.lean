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

open Nat

/-- `IsCarmichael n` : `n` is a Carmichael number, i.e. `n` is composite (greater than one and
not prime) and satisfies the conclusion of Fermat's little theorem for every base coprime
to `n`. -/

def ChernickTriplesInfinite : Prop :=
  ∀ N : ℕ, ∃ k > N, (6 * k + 1).Prime ∧ (12 * k + 1).Prime ∧ (18 * k + 1).Prime

/-- **Conditional reduction of the three-prime Carmichael infinitude problem.**
If Chernick's construction admits infinitely many admissible `k` (a special case of Dickson's
conjecture), then there are infinitely many Carmichael numbers with exactly three prime
factors. -/
