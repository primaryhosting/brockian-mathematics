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

namespace Brockian
namespace CarmichaelKorselt

/-- A *Carmichael number*: a composite `n > 1` which is a Fermat pseudoprime to every base,
i.e. `a ^ n ≡ a [MOD n]` for all `a`. -/

def ThreePrimeCarmichael : Set ℕ :=
  {n | IsCarmichael n ∧ ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p < q ∧ q < r ∧ n = p * q * r}

/-- **Conditional reduction.** Assuming the (open) Dickson-type hypothesis that the Chernick
triple `6k+1, 12k+1, 18k+1` is simultaneously prime for infinitely many `k`, there are
infinitely many Carmichael numbers with exactly three prime factors. -/
