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

namespace Brockian
namespace CarmichaelKorselt

/-- Korselt's criterion, used here as the definition of a Carmichael number:
`n` is composite (`1 < n` and not prime), squarefree, and `p - 1 ∣ n - 1` for every
prime `p` dividing `n`. -/

theorem isCarmichael_three_primes {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (dp : (p - 1) ∣ (p * q * r - 1)) (dq : (q - 1) ∣ (p * q * r - 1))
    (dr : (r - 1) ∣ (p * q * r - 1)) :
    IsCarmichael (p * q * r) ∧ (p * q * r).primeFactors.card = 3 := by
  have hp2 : 2 ≤ p := hp.two_le
  have hq2 : 2 ≤ q := hq.two_le
  have hr2 : 2 ≤ r := hr.two_le
  have hfac : (p * q * r).primeFactors = {p, q, r} := primeFactors_three hp hq hr
  have hsq : Squarefree (p * q * r) := squarefree_three hp hq hr hpq hpr hqr
  have hgt : 1 < p * q * r := by
    calc 1 < 2 * 2 * 2 := by norm_num
      _ ≤ p * q * r := Nat.mul_le_mul (Nat.mul_le_mul hp2 hq2) hr2
  refine ⟨⟨hgt, ?_, hsq, ?_⟩, ?_⟩
  · refine Nat.not_prime_mul ?_ (by omega)
    have : 2 * 2 ≤ p * q := Nat.mul_le_mul hp2 hq2
    omega
  · intro s hs
    rw [hfac] at hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · exact dp
    · exact dq
    · exact dr
  · rw [hfac, Finset.card_insert_of_notMem (by simp [hpq, hpr]),
      Finset.card_insert_of_notMem (by simp [hqr])]
    simp

/-- **Chernick's theorem**: if `6k+1`, `12k+1` and `18k+1` are all prime (with `k ≥ 1`),
then their product is a Carmichael number with exactly three prime factors. -/
