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
# Erdos Straus Conjecture
Category: Brockian Conjecture
Target: Brockian.ErdosStraus.ErdosStrausConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.ErdosStraus

/-- `ErdosStrausSolvable n` says that `4 / n` is a sum of three unit fractions with
positive natural denominators. -/

theorem erdosStrausConjecture_iff_primes :
    ErdosStrausConjecture ↔ ∀ p : ℕ, p.Prime → p % 24 = 1 → ErdosStrausSolvable p := by
  constructor
  · intro hc p hp _
    exact hc p hp.two_le
  · intro h n hn
    have hn0 : 0 < n := by omega
    have hp : (n.minFac).Prime := Nat.minFac_prime (by omega)
    have hdvd : n.minFac ∣ n := Nat.minFac_dvd n
    refine solvable_of_dvd hn0 hdvd ?_
    by_cases hm : n.minFac % 24 = 1
    · exact h _ hp hm
    · exact solvable_of_mod_24_ne_one hp.two_le hm

end Brockian.ErdosStraus

