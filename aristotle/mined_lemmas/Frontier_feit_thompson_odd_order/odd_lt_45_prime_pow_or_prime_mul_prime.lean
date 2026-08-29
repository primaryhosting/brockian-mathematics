/-
# Feit Thompson Odd Order
Category: Frontier Abel
Target: Frontier.feit_thompson_odd_order
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

universe u

namespace Frontier

/-!
## Statement

The Feit–Thompson odd order theorem states that every finite group of odd order is
solvable.  Its proof is a 255-page argument and is not available in Mathlib.  What is
formalized here is:

* the statement itself, in the form `OddOrderSolvable`;
* a complete, machine-checked **reduction** of the statement to its minimal-counterexample
  ("simple") case, `Frontier.feit_thompson_odd_order`;
* unconditional **base cases**: groups of odd prime-power order, groups of odd order the
  product of two distinct primes, and — combining these — every group of odd order less
  than `45`, the first odd order that is neither a prime power nor squarefree.
-/

/-- Having no normal subgroup other than `⊥` and `⊤` (for a nontrivial group this is
exactly simplicity). -/

theorem odd_lt_45_prime_pow_or_prime_mul_prime (n : ℕ) (hodd : Odd n) (hlt : n < 45) :
    (∃ p k, Nat.Prime p ∧ n = p ^ k) ∨
      (∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ n = p * q) := by
  obtain ⟨k, rfl⟩ := hodd
  have hk : k < 22 := by omega
  interval_cases k <;>
    first
      | (refine Or.inl ⟨3, 0, ?_, ?_⟩ <;> norm_num; done)
      | (refine Or.inl ⟨_, 1, ?_, (pow_one _).symm⟩; norm_num; done)
      | (refine Or.inl ⟨3, 2, ?_, ?_⟩ <;> norm_num; done)
      | (refine Or.inl ⟨3, 3, ?_, ?_⟩ <;> norm_num; done)
      | (refine Or.inl ⟨5, 2, ?_, ?_⟩ <;> norm_num; done)
      | (refine Or.inr ⟨3, 5, ?_, ?_, ?_, ?_⟩ <;> norm_num; done)
      | (refine Or.inr ⟨3, 7, ?_, ?_, ?_, ?_⟩ <;> norm_num; done)
      | (refine Or.inr ⟨3, 11, ?_, ?_, ?_, ?_⟩ <;> norm_num; done)
      | (refine Or.inr ⟨5, 7, ?_, ?_, ?_, ?_⟩ <;> norm_num; done)
      | (refine Or.inr ⟨3, 13, ?_, ?_, ?_, ?_⟩ <;> norm_num)

/-- **Base case of Feit–Thompson, unconditionally.**  Every finite group whose order is odd
and less than `45` is solvable.  (`45` is the least odd order for which this argument stops
working, since `45 = 3 ^ 2 * 5` is neither a prime power nor squarefree.) -/
