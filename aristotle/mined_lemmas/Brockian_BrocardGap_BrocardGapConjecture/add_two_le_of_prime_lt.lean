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
# Brocard Gap Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardGap.BrocardGapConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.BrocardGap

open Finset

/-- **Oppermann's conjecture**: for every `m > 1` there is a prime strictly between
`m² - m` and `m²`, and a prime strictly between `m²` and `m² + m`. -/

lemma add_two_le_of_prime_lt {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hp3 : 3 ≤ p)
    (hpq : p < q) : p + 2 ≤ q := by
  rcases Nat.lt_or_ge q (p + 2) with h | h
  · exfalso
    have hqe : q = p + 1 := by omega
    have hpodd : ¬ (2 ∣ p) := fun hdvd => by
      have := (Nat.Prime.eq_one_or_self_of_dvd hp 2 hdvd); omega
    have hqodd : ¬ (2 ∣ q) := fun hdvd => by
      have := (Nat.Prime.eq_one_or_self_of_dvd hq 2 hdvd)
      omega
    have hcases : 2 ∣ p ∨ 2 ∣ (p + 1) := by omega
    rcases hcases with h' | h'
    · exact hpodd h'
    · exact hqodd (hqe ▸ h')
  · exact h

/-- Key step: assuming Oppermann's conjecture, for odd primes `p < q` there are at least four
primes strictly between `p²` and `q²`. -/
