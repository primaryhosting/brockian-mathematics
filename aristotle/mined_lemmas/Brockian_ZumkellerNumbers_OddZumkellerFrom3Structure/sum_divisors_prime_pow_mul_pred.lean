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

set_option maxRecDepth 100000

namespace Brockian.ZumkellerNumbers

open Finset

/-- A positive natural number `n` is *Zumkeller* if its set of divisors can be split into
two blocks with equal sums. -/

theorem sum_divisors_prime_pow_mul_pred (p a : ℕ) (hp : p.Prime) :
    (∑ d ∈ (p ^ a).divisors, d) * (p - 1) + 1 = p ^ (a + 1) := by
  have hp1 : 1 ≤ p := hp.one_lt.le
  induction a with
  | zero => simp; omega
  | succ k ih =>
    rw [Nat.sum_divisors_prime_pow hp] at *
    rw [Finset.sum_range_succ, add_mul]
    have h2 : p ^ (k + 1) * (p - 1) + p ^ (k + 1) = p ^ (k + 1) * p := by
      rw [← Nat.mul_succ]; congr 1; omega
    have h3 : p ^ (k + 1 + 1) = p ^ (k + 1) * p := pow_succ p (k + 1)
    omega

/-- Divisor-sum bound for a prime power: `σ(p ^ a) * (p - 1) ≤ p ^ a * p`. -/
