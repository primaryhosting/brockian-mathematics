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

/-!
# Erdos Straus Conjecture
Category: Brockian Conjecture
Target: Brockian.ErdosStraus.ErdosStrausConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.ErdosStraus

/-- `Solvable n` says that `4 / n` can be written as a sum of three unit fractions
with positive natural denominators. -/

theorem erdosStrausConjecture_of_primes
    (H : ∀ p : ℕ, p.Prime → p % 12 = 1 → Solvable p) : ErdosStrausConjecture := by
  intro n hn
  have hn0 : 0 < n := by omega
  have hn1 : n ≠ 1 := by omega
  have hp : (n.minFac).Prime := Nat.minFac_prime hn1
  have hdvd : n.minFac ∣ n := Nat.minFac_dvd n
  by_cases h : n.minFac % 12 = 1
  · exact solvable_of_dvd hn0 hdvd (H _ hp h)
  · exact solvable_of_dvd hn0 hdvd (solvable_of_mod_twelve_ne_one _ hp.two_le h)

end Brockian.ErdosStraus

