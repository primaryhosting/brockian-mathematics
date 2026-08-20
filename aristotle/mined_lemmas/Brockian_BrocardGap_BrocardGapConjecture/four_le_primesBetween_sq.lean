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

lemma four_le_primesBetween_sq (hOpp : OppermannConjecture) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hp3 : 3 ≤ p) (hpq : p < q) :
    4 ≤ primesBetween (p * p) (q * q) := by
  have hq2 : p + 2 ≤ q := add_two_le_of_prime_lt hp hq hp3 hpq
  -- a prime in `(p², p² + p)`
  obtain ⟨-, ⟨a, ha, ha1, ha2⟩⟩ := hOpp p (by omega)
  -- primes in `((p+1)² - (p+1), (p+1)²)` and `((p+1)², (p+1)² + (p+1))`
  obtain ⟨⟨b, hb, hb1, hb2⟩, ⟨c, hc, hc1, hc2⟩⟩ := hOpp (p + 1) (by omega)
  -- a prime in `(q² - q, q²)`
  obtain ⟨⟨d, hd, hd1, hd2⟩, -⟩ := hOpp q (by omega)
  have hexp : (p + 1) * (p + 1) = p * p + 2 * p + 1 := by ring
  have hbb : (p + 1) * (p + 1) - (p + 1) = p * p + p := by omega
  have hqq : q * q - q = q * (q - 1) := by
    cases q with
    | zero => simp
    | succ n => simp [Nat.succ_mul, Nat.mul_succ]
  have hmul : (p + 2) * (p + 1) ≤ q * (q - 1) := Nat.mul_le_mul (by omega) (by omega)
  have hdd : p * p + 3 * p + 2 ≤ q * q - q := by nlinarith [hqq, hmul]
  exact four_le_primesBetween ha hb hc hd ha1 (by omega) (by omega) (by omega) hd2

/-- **Brocard's gap conjecture** (conditional reduction): assuming Oppermann's conjecture,
for every `n ≥ 1` there are at least four primes strictly between the squares of the
`n`-th and `(n+1)`-st primes (indices are 0-based, so `Nat.nth Nat.Prime 1 = 3`). -/
