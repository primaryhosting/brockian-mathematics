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
# Hyperperfect Infinitude
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.HyperperfectNumbers

open Finset

/-- `sigma n` is the sum of all divisors of `n`. -/

lemma isHyperperfect_of_prime_pair {p q k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : q + p = p * p + 1) (hk : k + 1 = p) : IsHyperperfect k (p * q) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hk0 : 0 < k := by omega
  have hqval : q = k * k + k + 1 := by
    subst hk; nlinarith [hpq]
  have hpne : p ≠ q := by
    intro h
    subst h
    nlinarith
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hpne
  have hs : sigma (p * q) = (p + 1) * (q + 1) := by
    rw [sigma_mul_of_coprime hcop, sigma_prime hp, sigma_prime hq]
  refine ⟨hk0, ?_, ?_⟩
  · have : 2 ≤ q := hq.two_le
    nlinarith
  · rw [hs, hqval, ← hk]
    ring

/-- `6` is `1`-hyperperfect (it is perfect). -/
