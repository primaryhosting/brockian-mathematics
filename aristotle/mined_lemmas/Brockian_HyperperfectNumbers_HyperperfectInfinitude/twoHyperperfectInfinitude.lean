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

/-- `IsKHyperperfect k n` states that `n` is a `k`-hyperperfect number, i.e. `k > 0`, `n > 1` and
`n = 1 + k * (σ n - n - 1)`, written here in the subtraction-free form
`k * σ n + 1 = (k + 1) * n + k`. -/

theorem twoHyperperfectInfinitude
    (H : ∀ N : ℕ, ∃ j p : ℕ, N < j ∧ Nat.Prime p ∧ p + 2 = 3 ^ (j + 1)) :
    {n : ℕ | IsKHyperperfect 2 n}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨j, p, hNj, hp, hpj⟩ := H N
  refine ⟨3 ^ j * p, ?_, ?_⟩
  · have := isKHyperperfect_pow_mul_prime (k := 2) (j := j) (p := p) two_pos (by norm_num)
      (by omega) hp (by simpa using hpj)
    simpa using this
  · have hj : N < 3 ^ j := lt_of_lt_of_le hNj (Nat.lt_pow_self (by norm_num)).le
    have h1 : 1 ≤ p := hp.one_lt.le.trans' (by norm_num)
    calc N < 3 ^ j := hj
      _ = 3 ^ j * 1 := (mul_one _).symm
      _ ≤ 3 ^ j * p := Nat.mul_le_mul_left _ h1

end Brockian.HyperperfectNumbers

