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

/-!
# Three Prime Carmichael Infinitude
Category: Brockian Conjecture
Target: Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

namespace Brockian.CarmichaelKorselt

/-- A Carmichael number: a composite `n > 1` which is a Fermat pseudoprime to every base
coprime to it. -/

def ThreePrimeCarmichaelSet : Set ℕ :=
  {n : ℕ | IsCarmichael n ∧ ∃ p q r : ℕ,
      p.Prime ∧ q.Prime ∧ r.Prime ∧ p < q ∧ q < r ∧ n = p * q * r}

/-- Chernick's hypothesis: there are infinitely many `k > 0` for which `6k+1`, `12k+1` and
`18k+1` are all prime. (This is a consequence of the Dickson / Hardy–Littlewood
prime `k`-tuple conjecture and is not known unconditionally.) -/
