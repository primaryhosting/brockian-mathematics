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
# Erdos Straus Conjecture
Category: Brockian Conjecture
Target: Brockian.ErdosStraus.ErdosStrausConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
`ErdosStrausConjecture` is a well-known open problem, so this file does not prove it
outright.  What is proved here, unconditionally and axiom-cleanly, is:

* `solvable_of_dvd`: solvability passes from a divisor to any positive multiple;
* explicit parametric solutions for `n` even, `3 ∣ n`, `n ≡ 3 (mod 4)`, `n ≡ 2 (mod 3)`
  and `n ≡ 5 (mod 8)`;
* `solvable_of_mod_24_ne_one`: the conjecture holds for every `n ≥ 2` with `n % 24 ≠ 1`;
* `erdosStrausConjecture_iff_primes`: the conjecture is *equivalent* to its special case
  for primes `p ≡ 1 (mod 24)`.
-/

namespace Brockian.ErdosStraus

/-- `Solvable n` says that `4 / n` can be written as a sum of three (not necessarily
distinct) positive unit fractions. -/

theorem erdosStrausConjecture_iff_primes :
    ErdosStrausConjecture ↔ ∀ p : ℕ, p.Prime → p % 24 = 1 → Solvable p := by
  constructor
  · intro h p hp _
    exact h p hp.two_le
  · intro h n hn
    have hn0 : 0 < n := by omega
    have hp : (n.minFac).Prime := Nat.minFac_prime (by omega)
    have hdvd : n.minFac ∣ n := Nat.minFac_dvd n
    by_cases hmod : n.minFac % 24 = 1
    · exact solvable_of_dvd hdvd hn0 (h _ hp hmod)
    · exact solvable_of_dvd hdvd hn0 (solvable_of_mod_24_ne_one hp.two_le hmod)

end Brockian.ErdosStraus

