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
# Odd Superperfect Exists
Category: Brockian Conjecture
Target: Brockian.SuperperfectNumbers.OddSuperperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset

namespace Brockian.SuperperfectNumbers

/-- The sum-of-divisors function `σ(n) = ∑_{d ∣ n} d`. -/

lemma sigma1_odd_of_even_exp {p e : ℕ} (hp : p.Prime) (hodd : p % 2 = 1) (he : Even e) :
    Odd (sigma1 (p ^ e)) := by
  rw [Nat.odd_iff, sigma1_primePow hp, Finset.sum_nat_mod]
  have h : ∀ i ∈ range (e + 1), p ^ i % 2 = 1 := by
    intro i _
    rw [Nat.pow_mod, hodd, one_pow]
    rfl
  rw [Finset.sum_congr rfl h]
  simp [Nat.add_mod, Nat.even_iff.mp he]

/-- For a prime `p ≡ 3 (mod 4)` and an odd exponent `e`, `σ(p^e)` is divisible by `4`. -/
