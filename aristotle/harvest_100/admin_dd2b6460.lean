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
# Andrica Conjecture
Category: Brockian Conjecture
Target: Brockian.AndricaConjecture.AndricaConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Andrica Conjecture
Category: Brockian Conjecture
Target: Brockian.AndricaConjecture.AndricaConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Andrica's conjecture states that for every `n`,
`√(p_{n+1}) - √(p_n) < 1`, where `p_n` denotes the `n`-th prime.
This is an open problem, so the statement itself is recorded as a `Prop`
(`AndricaConjecture`), and what is proved here are:

* an exact reformulation as a bound on prime gaps (`andrica_iff_gap`,
  `andrica_iff_gap_lt`);
* a conditional reduction to a purely arithmetic gap bound
  (`andrica_of_natSqrt_gap`);
* an unconditional verification of the conjecture for the first 25 gaps
  (`andrica_of_lt_25`).

No lemma in Mathlib proves Andrica's conjecture. The Mathlib input used below
is `Nat.nth Nat.Prime` (the `n`-th prime, cf. `Nat.prime_nth_prime`,
`Nat.nth_count`) together with the `Real.sqrt` API
(`Real.sqrt_lt'`, `Real.sq_sqrt`, `Real.nat_sqrt_le_real_sqrt`).
-/

namespace Brockian.AndricaConjecture

open Real

/-- **Andrica's conjecture**: consecutive primes satisfy
`√(p_{n+1}) - √(p_n) < 1`, where `p_n = Nat.nth Nat.Prime n` is the `n`-th
prime (indexed from `p_0 = 2`). -/
def AndricaConjecture : Prop :=
  ∀ n : ℕ, √(Nat.nth Nat.Prime (n + 1)) - √(Nat.nth Nat.Prime n) < 1

/-- Elementary reformulation: for a nonnegative real `a`, `√b - √a < 1` iff
`b < a + 2√a + 1`. -/
theorem sqrt_sub_sqrt_lt_one_iff {a b : ℝ} (ha : 0 ≤ a) :
    √b - √a < 1 ↔ b < a + 2 * √a + 1 := by
  have hpos : (0 : ℝ) < √a + 1 := by positivity
  rw [sub_lt_iff_lt_add, add_comm (1 : ℝ) (√a), Real.sqrt_lt' hpos]
  have hsq : (√a + 1) ^ 2 = a + 2 * √a + 1 := by
    have h := Real.sq_sqrt ha
    nlinarith [h]
  rw [hsq]

/-- Andrica's conjecture is equivalent to the prime-gap bound
`p_{n+1} < p_n + 2√(p_n) + 1`. -/
theorem andrica_iff_gap :
    AndricaConjecture ↔
      ∀ n : ℕ, (Nat.nth Nat.Prime (n + 1) : ℝ) <
        (Nat.nth Nat.Prime n : ℝ) + 2 * √(Nat.nth Nat.Prime n) + 1 := by
  constructor
  · intro h n
    exact (sqrt_sub_sqrt_lt_one_iff (a := (Nat.nth Nat.Prime n : ℝ))
      (b := (Nat.nth Nat.Prime (n + 1) : ℝ)) (Nat.cast_nonneg _)).1 (h n)
  · intro h n
    exact (sqrt_sub_sqrt_lt_one_iff (a := (Nat.nth Nat.Prime n : ℝ))
      (b := (Nat.nth Nat.Prime (n + 1) : ℝ)) (Nat.cast_nonneg _)).2 (h n)

/-- Andrica's conjecture is equivalent to the prime-gap bound
`p_{n+1} - p_n < 2√(p_n) + 1`. -/
theorem andrica_iff_gap_lt :
    AndricaConjecture ↔
      ∀ n : ℕ, (Nat.nth Nat.Prime (n + 1) : ℝ) - (Nat.nth Nat.Prime n : ℝ) <
        2 * √(Nat.nth Nat.Prime n) + 1 := by
  rw [andrica_iff_gap]
  constructor <;> intro h n <;> have := h n <;> linarith

/-- A purely arithmetic sufficient condition: if `b ≤ a + 2 * Nat.sqrt a`
then `√b - √a < 1`. -/
theorem sqrt_sub_sqrt_lt_one_of_natSqrt {a b : ℕ} (h : b ≤ a + 2 * Nat.sqrt a) :
    √(b : ℝ) - √(a : ℝ) < 1 := by
  rw [sqrt_sub_sqrt_lt_one_iff (Nat.cast_nonneg a)]
  have h1 : (b : ℝ) ≤ (a : ℝ) + 2 * (Nat.sqrt a : ℝ) := by exact_mod_cast h
  have h2 : (Nat.sqrt a : ℝ) ≤ √(a : ℝ) := Real.nat_sqrt_le_real_sqrt
  linarith

/-- Conditional reduction: Andrica's conjecture follows from the integer prime
gap bound `p_{n+1} ≤ p_n + 2 * ⌊√(p_n)⌋`. -/
theorem andrica_of_natSqrt_gap
    (h : ∀ n : ℕ, Nat.nth Nat.Prime (n + 1) ≤
      Nat.nth Nat.Prime n + 2 * Nat.sqrt (Nat.nth Nat.Prime n)) :
    AndricaConjecture := fun n => sqrt_sub_sqrt_lt_one_of_natSqrt (h n)

/-- Pointwise conditional form: at a given index `n`, the arithmetic gap bound
`p_{n+1} ≤ p_n + 2 * ⌊√(p_n)⌋` implies Andrica's inequality at `n`. -/
theorem andrica_at_of_natSqrt_gap (n : ℕ)
    (h : Nat.nth Nat.Prime (n + 1) ≤
      Nat.nth Nat.Prime n + 2 * Nat.sqrt (Nat.nth Nat.Prime n)) :
    √(Nat.nth Nat.Prime (n + 1)) - √(Nat.nth Nat.Prime n) < 1 :=
  sqrt_sub_sqrt_lt_one_of_natSqrt h

/-- Conditional reduction from the (also open) gap conjecture
`p_{n+1} - p_n ≤ √(p_n)`. -/
theorem andrica_of_sqrt_gap_bound
    (h : ∀ n : ℕ, (Nat.nth Nat.Prime (n + 1) : ℝ) - Nat.nth Nat.Prime n ≤
      √(Nat.nth Nat.Prime n)) :
    AndricaConjecture := by
  rw [andrica_iff_gap_lt]
  intro n
  have h1 := h n
  have h2 : (0 : ℝ) ≤ √(Nat.nth Nat.Prime n) := Real.sqrt_nonneg _
  linarith

/-- Helper: identify the `k`-th prime from a primality certificate and a
count computation. -/
theorem nth_prime_eq_of_count {k q : ℕ} (hq : Nat.Prime q)
    (hcount : Nat.count Nat.Prime q = k) : Nat.nth Nat.Prime k = q :=
  hcount ▸ Nat.nth_count hq

/-- Instance of Andrica's conjecture at `n`, given the values of `p_n` and
`p_{n+1}` and the arithmetic gap bound. -/
theorem andrica_at_of_values {n a b : ℕ} (ha : Nat.nth Nat.Prime n = a)
    (hb : Nat.nth Nat.Prime (n + 1) = b) (h : b ≤ a + 2 * Nat.sqrt a) :
    √(Nat.nth Nat.Prime (n + 1)) - √(Nat.nth Nat.Prime n) < 1 := by
  rw [ha, hb]
  exact sqrt_sub_sqrt_lt_one_of_natSqrt h

section Values

set_option maxRecDepth 40000

theorem nth_prime_0 : Nat.nth Nat.Prime 0 = 2 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
theorem nth_prime_1 : Nat.nth Nat.Prime 1 = 3 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
theorem nth_prime_2 : Nat.nth Nat.Prime 2 = 5 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
theorem nth_prime_3 : Nat.nth Nat.Prime 3 = 7 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
theorem nth_prime_4 : Nat.nth Nat.Prime 4 = 11 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
theorem nth_prime_5 : Nat.nth Nat.Prime 5 = 13 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
theorem nth_prime_6 : Nat.nth Nat.Prime 6 = 17 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
theorem nth_prime_7 : Nat.nth Nat.Prime 7 = 19 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
theorem nth_prime_8 : Nat.nth Nat.Prime 8 = 23 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
theorem nth_prime_9 : Nat.nth Nat.Prime 9 = 29 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
theorem nth_prime_10 : Nat.nth Nat.Prime 10 = 31 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
theorem nth_prime_11 : Nat.nth Nat.Prime 11 = 37 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
theorem nth_prime_12 : Nat.nth Nat.Prime 12 = 41 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
theorem nth_prime_13 : Nat.nth Nat.Prime 13 = 43 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
theorem nth_prime_14 : Nat.nth Nat.Prime 14 = 47 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
theorem nth_prime_15 : Nat.nth Nat.Prime 15 = 53 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
theorem nth_prime_16 : Nat.nth Nat.Prime 16 = 59 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
theorem nth_prime_17 : Nat.nth Nat.Prime 17 = 61 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
theorem nth_prime_18 : Nat.nth Nat.Prime 18 = 67 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
theorem nth_prime_19 : Nat.nth Nat.Prime 19 = 71 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
theorem nth_prime_20 : Nat.nth Nat.Prime 20 = 73 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
theorem nth_prime_21 : Nat.nth Nat.Prime 21 = 79 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
theorem nth_prime_22 : Nat.nth Nat.Prime 22 = 83 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
theorem nth_prime_23 : Nat.nth Nat.Prime 23 = 89 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
theorem nth_prime_24 : Nat.nth Nat.Prime 24 = 97 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
theorem nth_prime_25 : Nat.nth Nat.Prime 25 = 101 :=
  nth_prime_eq_of_count (by norm_num) (by decide)

end Values

/-- Unconditional partial result: Andrica's conjecture holds for the first
25 prime gaps, i.e. for all `n < 25` (the primes `2` through `101`). -/
theorem andrica_of_lt_25 (n : ℕ) (hn : n < 25) :
    √(Nat.nth Nat.Prime (n + 1)) - √(Nat.nth Nat.Prime n) < 1 := by
  interval_cases n
  · exact andrica_at_of_values nth_prime_0 nth_prime_1 (by norm_num)
  · exact andrica_at_of_values nth_prime_1 nth_prime_2 (by norm_num)
  · exact andrica_at_of_values nth_prime_2 nth_prime_3 (by norm_num)
  · exact andrica_at_of_values nth_prime_3 nth_prime_4 (by norm_num)
  · exact andrica_at_of_values nth_prime_4 nth_prime_5 (by norm_num)
  · exact andrica_at_of_values nth_prime_5 nth_prime_6 (by norm_num)
  · exact andrica_at_of_values nth_prime_6 nth_prime_7 (by norm_num)
  · exact andrica_at_of_values nth_prime_7 nth_prime_8 (by norm_num)
  · exact andrica_at_of_values nth_prime_8 nth_prime_9 (by norm_num)
  · exact andrica_at_of_values nth_prime_9 nth_prime_10 (by norm_num)
  · exact andrica_at_of_values nth_prime_10 nth_prime_11 (by norm_num)
  · exact andrica_at_of_values nth_prime_11 nth_prime_12 (by norm_num)
  · exact andrica_at_of_values nth_prime_12 nth_prime_13 (by norm_num)
  · exact andrica_at_of_values nth_prime_13 nth_prime_14 (by norm_num)
  · exact andrica_at_of_values nth_prime_14 nth_prime_15 (by norm_num)
  · exact andrica_at_of_values nth_prime_15 nth_prime_16 (by norm_num)
  · exact andrica_at_of_values nth_prime_16 nth_prime_17 (by norm_num)
  · exact andrica_at_of_values nth_prime_17 nth_prime_18 (by norm_num)
  · exact andrica_at_of_values nth_prime_18 nth_prime_19 (by norm_num)
  · exact andrica_at_of_values nth_prime_19 nth_prime_20 (by norm_num)
  · exact andrica_at_of_values nth_prime_20 nth_prime_21 (by norm_num)
  · exact andrica_at_of_values nth_prime_21 nth_prime_22 (by norm_num)
  · exact andrica_at_of_values nth_prime_22 nth_prime_23 (by norm_num)
  · exact andrica_at_of_values nth_prime_23 nth_prime_24 (by norm_num)
  · exact andrica_at_of_values nth_prime_24 nth_prime_25 (by norm_num)

end Brockian.AndricaConjecture

