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
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Brockian.ZumkellerNumbers

/-- A positive integer `n` is a *Zumkeller number* if its set of divisors can be split into
two parts with equal sums, i.e. there is a set `A` of divisors of `n` whose sum is exactly
half of `σ(n)`. -/

lemma four_sigma_lt_five {q : ℕ} (hq : q.Prime) (h5 : 5 ≤ q) (b : ℕ) :
    4 * ∑ d ∈ (q ^ b).divisors, d < 5 * q ^ b := by
  have hS : ∑ d ∈ (q ^ b : ℕ).divisors, d = ∑ i ∈ Finset.range (b + 1), q ^ i :=
    Nat.sum_divisors_prime_pow hq
  rw [hS]
  set S := ∑ i ∈ Finset.range (b + 1), q ^ i with hSdef
  have hid := pow_mul_geom q b
  have hpos : 0 < q ^ b := pow_pos (by omega) b
  have hSpos : 0 < S := by
    rw [hSdef]
    exact Finset.sum_pos (fun i _ => pow_pos (by omega) i) ⟨0, by simp⟩
  have hpow : q ^ (b + 1) = q * q ^ b := by ring
  nlinarith [hid, hpow]

/-- A product of two odd prime powers with distinct primes is deficient. -/
