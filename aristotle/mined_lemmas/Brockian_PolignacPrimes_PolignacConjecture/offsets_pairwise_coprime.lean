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
# Polignac Conjecture
Category: Brockian Conjecture
Target: Brockian.PolignacPrimes.PolignacConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Polignac Conjecture
Category: Brockian Conjecture
Target: Brockian.PolignacPrimes.PolignacConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean requires `import` to precede any module docstring, so the required header
-- comment appears both at the very top of the file (as a plain comment) and, verbatim,
-- as the module docstring just above.

namespace Brockian.PolignacPrimes

open Nat

/-- `PolignacPair p n` says that `p` and `p + n` are *consecutive* primes:
both are prime and no number strictly between them is prime. -/

lemma offsets_pairwise_coprime :
    (offsets n).Pairwise (Function.onFun Nat.Coprime (auxPrime n)) := by
  have hnd : (offsets n).Nodup := by
    simpa [offsets] using List.nodup_range' (s := 1) (n := n - 1)
  refine List.Nodup.pairwise_of_forall_ne hnd ?_
  intro i _ j _ hij
  exact (Nat.coprime_primes (auxPrime_prime n i) (auxPrime_prime n j)).2
    (fun h => hij (auxPrime_injective n h))

/-- The starting point of the arithmetic progression: a solution of the
simultaneous congruences `B ≡ -j (mod auxPrime n j)` for `1 ≤ j ≤ n - 1`. -/
