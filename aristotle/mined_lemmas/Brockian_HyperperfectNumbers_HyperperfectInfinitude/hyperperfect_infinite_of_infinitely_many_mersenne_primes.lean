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

theorem hyperperfect_infinite_of_infinitely_many_mersenne_primes
    (H : ∀ N : ℕ, ∃ k, N < k ∧ (2 ^ (k + 1) - 1).Prime) : Hyperperfect.Infinite := by
  refine Set.infinite_of_forall_exists_gt ?_
  intro N
  obtain ⟨k, hkN, hq⟩ := H N
  set q := 2 ^ (k + 1) - 1 with hqdef
  have h1 : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  have hqk : q + 1 = 2 ^ (k + 1) := by omega
  have hk1 : 1 ≤ k := by omega
  refine ⟨2 ^ k * q, ⟨1, isHyperperfect_one_two_pow_mul_mersenne hq hqk hk1⟩, ?_⟩
  have hq3 : 3 ≤ q := by
    have h4 : (4 : ℕ) ≤ 2 ^ (k + 1) := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hkk : k < 2 ^ k := Nat.lt_two_pow_self
  calc N < k := hkN
    _ < 2 ^ k := hkk
    _ ≤ 2 ^ k * q := Nat.le_mul_of_pos_right _ (by omega)

end Brockian.HyperperfectNumbers

