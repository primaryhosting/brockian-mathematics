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
# Even Perfect Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.EvenPerfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
## Overview

Whether there are infinitely many even perfect numbers is a well-known open problem: by the
Euclid–Euler theorem it is *equivalent* to the existence of infinitely many Mersenne primes,
which is itself open.  Accordingly, what is proved here is the (unconditional, Lean-checked)
reduction:

* `Brockian.MersennePerfect.EvenPerfectInfinitude` :
  if there are infinitely many exponents `p` with `mersenne p = 2 ^ p - 1` prime, then the set
  of even perfect numbers is infinite.

The file is self-contained over Mathlib: Euclid's direction of the Euclid–Euler theorem
(a Mersenne prime yields an even perfect number) is proved here from scratch.
-/

namespace Brockian.MersennePerfect

open ArithmeticFunction Finset

-- access notation `σ`
open scoped sigma

/-- The set of exponents `p` for which the Mersenne number `2 ^ p - 1` is prime. -/
def mersennePrimeExponents : Set ℕ := {p : ℕ | (mersenne p).Prime}

/-- The set of even perfect numbers. -/
def evenPerfects : Set ℕ := {n : ℕ | Even n ∧ Nat.Perfect n}

/-- The sum of divisors of `2 ^ k` is the Mersenne number `2 ^ (k + 1) - 1`. -/
theorem sigma_two_pow (k : ℕ) : σ 1 (2 ^ k) = mersenne (k + 1) := by
  simp_rw [sigma_one_apply, mersenne, ← one_add_one_eq_two, ← geom_sum_mul_add 1 (k + 1)]
  norm_num

/-- **Euclid's direction**: if `mersenne (k + 1)` is prime, then `2 ^ k * mersenne (k + 1)`
is a perfect number. -/
theorem perfect_two_pow_mul_mersenne {k : ℕ} (pr : (mersenne (k + 1)).Prime) :
    Nat.Perfect (2 ^ k * mersenne (k + 1)) := by
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul, ← mul_assoc, ← pow_succ', ← sigma_one_apply,
    mul_comm, isMultiplicative_sigma.map_mul_of_coprime
      ((Odd.coprime_two_right (by simp)).pow_right _), sigma_two_pow]
  · simp [pr, sigma_one_apply]
  · positivity

/-- If `mersenne (k + 1)` is prime then `k ≠ 0`, since `mersenne 1 = 1` is not prime. -/
theorem exponent_ne_zero {k : ℕ} (pr : (mersenne (k + 1)).Prime) : k ≠ 0 := by
  rintro rfl
  simp [mersenne, Nat.not_prime_one] at pr

/-- The perfect number produced by Euclid's construction is even. -/
theorem even_two_pow_mul_mersenne {k : ℕ} (pr : (mersenne (k + 1)).Prime) :
    Even (2 ^ k * mersenne (k + 1)) := by
  simp [exponent_ne_zero pr, parity_simps]

/-- Euclid's construction lands in the set of even perfect numbers. -/
theorem mem_evenPerfects {k : ℕ} (pr : (mersenne (k + 1)).Prime) :
    2 ^ k * mersenne (k + 1) ∈ evenPerfects :=
  ⟨even_two_pow_mul_mersenne pr, perfect_two_pow_mul_mersenne pr⟩

/-- Euclid's construction is at least as large as its exponent, which makes it easy to see
that distinct large Mersenne primes give arbitrarily large perfect numbers. -/
theorem le_two_pow_mul_mersenne (k : ℕ) :
    k + 1 ≤ 2 ^ k * mersenne (k + 1) := by
  have h1 : 1 ≤ mersenne (k + 1) := mersenne_pos.2 k.succ_pos
  have h2 : k + 1 ≤ 2 ^ k := Nat.succ_le_of_lt (Nat.lt_two_pow_self)
  calc k + 1 ≤ 2 ^ k := h2
    _ = 2 ^ k * 1 := (mul_one _).symm
    _ ≤ 2 ^ k * mersenne (k + 1) := Nat.mul_le_mul_left _ h1

/-- **Even Perfect Infinitude (conditional reduction).**
If there are infinitely many Mersenne primes, then there are infinitely many even perfect
numbers.  (The hypothesis is the still-open infinitude of Mersenne primes; by the
Euclid–Euler theorem the two statements are in fact equivalent.) -/
theorem EvenPerfectInfinitude (h : mersennePrimeExponents.Infinite) : evenPerfects.Infinite := by
  refine Set.infinite_of_not_bddAbove ?_
  rintro ⟨M, hM⟩
  obtain ⟨p, hp, hpM⟩ := h.exists_gt (M + 1)
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  have hmem := mem_evenPerfects hp
  have hle : 2 ^ k * mersenne (k + 1) ≤ M := hM hmem
  have := le_two_pow_mul_mersenne k
  omega

end Brockian.MersennePerfect

/-
# Even Perfect Infinitude — the Euler converse
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.evenPerfects_infinite_iff
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import RequestProject.Brockian.MersennePerfect
import Archive.Wiedijk100Theorems.PerfectNumbers

/-!
## Overview

`RequestProject/Brockian/MersennePerfect.lean` proves, over Mathlib alone, that infinitely many
Mersenne primes give infinitely many even perfect numbers.  Here we add the converse, using
Euler's half of the Euclid–Euler theorem (available in Mathlib's `Archive`), obtaining the
equivalence

  `evenPerfects.Infinite ↔ mersennePrimeExponents.Infinite`.

Both sides are open problems; this file records that they are the same problem.
-/

namespace Brockian.MersennePerfect

/-- Every even perfect number is `2 ^ (p - 1) * mersenne p` for some Mersenne prime exponent
`p`; i.e. `evenPerfects` is contained in the image of `mersennePrimeExponents` under Euclid's
construction. -/
theorem evenPerfects_subset_image :
    evenPerfects ⊆ (fun p : ℕ => 2 ^ (p - 1) * mersenne p) '' mersennePrimeExponents := by
  rintro n ⟨ev, perf⟩
  obtain ⟨k, pr, rfl⟩ :=
    Theorems100.Nat.eq_two_pow_mul_prime_mersenne_of_even_perfect ev perf
  exact ⟨k + 1, pr, by simp⟩

/-- **Euler's converse**: if there are infinitely many even perfect numbers, then there are
infinitely many Mersenne primes. -/
theorem mersennePrimeExponents_infinite_of_evenPerfects_infinite
    (h : evenPerfects.Infinite) : mersennePrimeExponents.Infinite := by
  by_contra hcon
  rw [Set.not_infinite] at hcon
  exact h ((hcon.image _).subset evenPerfects_subset_image)

/-- **Euclid–Euler infinitude equivalence**: there are infinitely many even perfect numbers if
and only if there are infinitely many Mersenne primes.  Both statements are open. -/
theorem evenPerfects_infinite_iff :
    evenPerfects.Infinite ↔ mersennePrimeExponents.Infinite :=
  ⟨mersennePrimeExponents_infinite_of_evenPerfects_infinite, EvenPerfectInfinitude⟩

end Brockian.MersennePerfect

