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
/-!
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

open scoped BigOperators

namespace Brockian
namespace ZumkellerNumbers

/-- A positive natural number `n` is *Zumkeller* if its set of divisors can be split into
two blocks having the same sum. -/

theorem not_isZumkeller_odd_prime_pow {p a : ℕ} (hp : p.Prime) (hpodd : Odd p) :
    ¬ IsZumkeller (p ^ a) := by
  intro hz
  have hodd : Odd (p ^ a) := hpodd.pow
  have h3 := OddZumkellerFrom3Structure hodd hz
  have hsub : (p ^ a).primeFactors ⊆ {p} := by
    intro q hq
    simp only [Finset.mem_singleton]
    exact (Nat.prime_dvd_prime_iff_eq (Nat.prime_of_mem_primeFactors hq) hp).1
      ((Nat.prime_of_mem_primeFactors hq).dvd_of_dvd_pow (Nat.dvd_of_mem_primeFactors hq))
  have := Finset.card_le_card hsub
  simp only [Finset.card_singleton] at this
  omega

end ZumkellerNumbers
end Brockian

