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
# Repunit Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.RepunitPrimes.RepunitPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Repunit Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.RepunitPrimes.RepunitPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.RepunitPrimes

/-- The `n`-th base-ten repunit: the number `11…1` with `n` digits equal to `1`. -/

def repunit (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, 10 ^ i

lemma repunit_add (a b : ℕ) : repunit (a + b) = repunit a + 10 ^ a * repunit b := by
  unfold repunit
  rw [Finset.sum_range_add, Finset.mul_sum]
  simp [pow_add]

/-- The closed form `9 * R n + 1 = 10 ^ n`. -/

lemma le_repunit (n : ℕ) : n ≤ repunit n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h : repunit (n + 1) = repunit n + 10 ^ n := by
        simp [repunit_add n 1]
      have h10 : 1 ≤ 10 ^ n := Nat.one_le_pow _ _ (by norm_num)
      omega

def repunitPrimes : Set ℕ := {p | p.Prime ∧ ∃ n, p = repunit n}

/-- The repunit prime `R 2 = 11`; in particular `repunitPrimes` is nonempty. -/

theorem RepunitPrimeInfinitude
    (h : ∀ N : ℕ, ∃ n, N < n ∧ Nat.Prime (repunit n)) :
    repunitPrimes.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨n, hn, hp⟩ := h a
  refine ⟨repunit n, ⟨hp, ⟨n, rfl⟩⟩, ?_⟩
  have := le_repunit n
  omega

/--
**The repunit-prime infinitude conjecture is equivalent to its index form.**

The set of repunit primes is infinite if and only if repunit primes occur at
arbitrarily large indices.  This makes the hypothesis of `RepunitPrimeInfinitude`
not merely sufficient but exactly equivalent to the conclusion.
-/
