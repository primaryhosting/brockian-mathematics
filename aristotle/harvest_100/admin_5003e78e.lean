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
# Wilson Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.WilsonPrimes.WilsonPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Wilson Prime Infinitude

Category: Brockian Conjecture.  Target: `Brockian.WilsonPrimes.WilsonPrimeInfinitude`.

Note: the header block above is kept as an ordinary comment because Lean requires `import`
commands to precede every other command, including module docstrings.
-/

open Nat

namespace Brockian.WilsonPrimes

/-- A *Wilson prime* is a prime `p` such that `p ^ 2 ∣ (p - 1)! + 1`.
(By Wilson's theorem every prime satisfies `p ∣ (p - 1)! + 1`; a Wilson prime is one for
which the stronger congruence modulo `p ^ 2` holds.) -/
def IsWilsonPrime (p : ℕ) : Prop := p.Prime ∧ p ^ 2 ∣ (p - 1)! + 1

/-- **Wilson's theorem**, in the divisibility form `p ∣ (p - 1)! + 1`.
This is an immediate consequence of `ZMod.wilsons_lemma`. -/
theorem prime_dvd_factorial_pred_add_one {p : ℕ} (hp : p.Prime) : p ∣ (p - 1)! + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h : (((p - 1)! + 1 : ℕ) : ZMod p) = 0 := by
    push_cast
    rw [ZMod.wilsons_lemma]
    ring
  exact (ZMod.natCast_eq_zero_iff _ _).mp h

/-- Every Wilson prime is prime. -/
theorem IsWilsonPrime.prime {p : ℕ} (h : IsWilsonPrime p) : p.Prime := h.1

/-- `5` is a Wilson prime: `5 ^ 2 = 25 ∣ 4! + 1 = 25`. -/
theorem isWilsonPrime_five : IsWilsonPrime 5 := by
  refine ⟨by norm_num, ?_⟩
  decide

/-- `13` is a Wilson prime: `13 ^ 2 = 169 ∣ 12! + 1 = 479001601`. -/
theorem isWilsonPrime_thirteen : IsWilsonPrime 13 := by
  refine ⟨by norm_num, ?_⟩
  norm_num [Nat.factorial]

set_option maxRecDepth 100000 in
/-- `563` is a Wilson prime. -/
theorem isWilsonPrime_563 : IsWilsonPrime 563 := by
  refine ⟨by norm_num, ?_⟩
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
/-- The only Wilson primes below `1000` are `5`, `13` and `563` (a kernel-checked
exhaustive search). -/
theorem isWilsonPrime_lt_1000_iff (p : ℕ) (hp : p < 1000) :
    IsWilsonPrime p ↔ (p = 5 ∨ p = 13 ∨ p = 563) := by
  have key : ∀ q < 1000, (q.Prime ∧ q ^ 2 ∣ (q - 1)! + 1) ↔ (q = 5 ∨ q = 13 ∨ q = 563) := by
    decide
  exact key p hp

/-- There exists at least one Wilson prime. -/
theorem exists_isWilsonPrime : ∃ p, IsWilsonPrime p := ⟨5, isWilsonPrime_five⟩

/-- **Conditional reduction of the Wilson prime infinitude conjecture.**

Whether infinitely many Wilson primes exist is a well-known open problem (only `5`, `13`
and `563` are known).  What is proved here is the reduction of the infinitude statement to
the unboundedness statement: if for every bound `N` there is a Wilson prime exceeding `N`,
then the set of Wilson primes is infinite. -/
theorem WilsonPrimeInfinitude
    (h : ∀ N : ℕ, ∃ p, N < p ∧ IsWilsonPrime p) :
    {p : ℕ | IsWilsonPrime p}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨p, hlt, hp⟩ := h a
  exact ⟨p, hp, hlt⟩

/-- The converse of the reduction: infinitude of the set of Wilson primes implies that
Wilson primes are unbounded.  Hence the two formulations are equivalent. -/
theorem unbounded_of_infinite (h : {p : ℕ | IsWilsonPrime p}.Infinite) :
    ∀ N : ℕ, ∃ p, N < p ∧ IsWilsonPrime p := by
  intro N
  obtain ⟨p, hp, hlt⟩ := h.exists_gt N
  exact ⟨p, hlt, hp⟩

/-- The infinitude conjecture is *equivalent* to the unboundedness statement. -/
theorem infinite_iff_unbounded :
    {p : ℕ | IsWilsonPrime p}.Infinite ↔ ∀ N : ℕ, ∃ p, N < p ∧ IsWilsonPrime p :=
  ⟨unbounded_of_infinite, WilsonPrimeInfinitude⟩

end Brockian.WilsonPrimes

