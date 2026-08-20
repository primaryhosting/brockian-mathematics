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
-- (The header above uses `/- -/` rather than `/-! -/` because Lean 4 does not allow a
-- module docstring to precede the `import` line.)

import Mathlib

namespace Brockian.AndricaConjecture

open scoped Nat

/-! ## The sequence of primes -/

/-- The set of primes is infinite. -/
theorem setOf_prime_infinite : {n : ℕ | Nat.Prime n}.Infinite :=
  Nat.infinite_setOf_prime

/-- `nthPrime n` is the `n`-th prime number (`nthPrime 0 = 2`). -/
noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

theorem nthPrime_prime (n : ℕ) : Nat.Prime (nthPrime n) :=
  Nat.nth_mem_of_infinite setOf_prime_infinite n

theorem two_le_nthPrime (n : ℕ) : 2 ≤ nthPrime n := (nthPrime_prime n).two_le

theorem nthPrime_lt_nthPrime_succ (n : ℕ) : nthPrime n < nthPrime (n + 1) :=
  Nat.nth_lt_nth setOf_prime_infinite |>.mpr (Nat.lt_succ_self n)

/-- `nthPrime (n+1)` is the least prime exceeding `nthPrime n`. -/
theorem nthPrime_succ_le {n q : ℕ} (hq : Nat.Prime q) (h : nthPrime n < q) :
    nthPrime (n + 1) ≤ q := by
  by_contra hcon
  push_neg at hcon
  exact absurd (Nat.le_nth_of_lt_nth_succ hcon hq) (not_le.mpr h)

/-! ## Statements -/

/-- **Andrica's conjecture**: consecutive primes satisfy `√p_{n+1} - √p_n < 1`. -/
def AndricaStatement : Prop :=
  ∀ n : ℕ, Real.sqrt (nthPrime (n + 1)) - Real.sqrt (nthPrime n) < 1

/-- **Oppermann's conjecture**: for every `m ≥ 2` there is a prime strictly between
`m² - m` and `m²`, and a prime strictly between `m²` and `m² + m`. -/
def OppermannConjecture : Prop :=
  ∀ m : ℕ, 2 ≤ m →
    (∃ q, Nat.Prime q ∧ m ^ 2 - m < q ∧ q < m ^ 2) ∧
    (∃ q, Nat.Prime q ∧ m ^ 2 < q ∧ q < m ^ 2 + m)

/-! ## An unconditional reformulation -/

/-- Andrica's inequality at `n` is equivalent to the prime-gap bound
`p_{n+1} < p_n + 2√p_n + 1`. -/
theorem andrica_iff_gap (n : ℕ) :
    Real.sqrt (nthPrime (n + 1)) - Real.sqrt (nthPrime n) < 1 ↔
      (nthPrime (n + 1) : ℝ) < (nthPrime n : ℝ) + 2 * Real.sqrt (nthPrime n) + 1 := by
  have hP : (0 : ℝ) ≤ (nthPrime n : ℝ) := Nat.cast_nonneg _
  have hpos : (0 : ℝ) < Real.sqrt (nthPrime n) + 1 := by positivity
  have hsq : Real.sqrt (nthPrime n) ^ 2 = (nthPrime n : ℝ) := Real.sq_sqrt hP
  constructor
  · intro h
    have h1 : Real.sqrt (nthPrime (n + 1)) < Real.sqrt (nthPrime n) + 1 := by linarith
    have h2 := (Real.sqrt_lt' hpos).mp h1
    nlinarith [h2, hsq]
  · intro h
    have h1 : (nthPrime (n + 1) : ℝ) < (Real.sqrt (nthPrime n) + 1) ^ 2 := by nlinarith [hsq]
    have h2 := (Real.sqrt_lt' hpos).mpr h1
    linarith

/-- **Unconditional partial result.** If `k² ≤ p_n` and the prime gap satisfies
`p_{n+1} - p_n ≤ 2k`, then Andrica's inequality holds at `n`. -/
theorem andrica_of_gap_le_two_mul (n k : ℕ) (hk : k ^ 2 ≤ nthPrime n)
    (h : nthPrime (n + 1) ≤ nthPrime n + 2 * k) :
    Real.sqrt (nthPrime (n + 1)) - Real.sqrt (nthPrime n) < 1 := by
  rw [andrica_iff_gap]
  have hcast : (nthPrime (n + 1) : ℝ) ≤ (nthPrime n : ℝ) + 2 * (k : ℝ) := by exact_mod_cast h
  have hkr : (k : ℝ) ≤ Real.sqrt (nthPrime n) := by
    rw [show ((k : ℕ) : ℝ) = Real.sqrt (((k : ℕ) : ℝ) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hk)
  linarith

/-- **Unconditional partial result.** Andrica's inequality holds at every index `n`
whose prime gap satisfies `p_{n+1} - p_n ≤ 2⌊√p_n⌋`. -/
theorem andrica_of_gap_le (n : ℕ)
    (h : nthPrime (n + 1) ≤ nthPrime n + 2 * Nat.sqrt (nthPrime n)) :
    Real.sqrt (nthPrime (n + 1)) - Real.sqrt (nthPrime n) < 1 :=
  andrica_of_gap_le_two_mul n (Nat.sqrt (nthPrime n))
    (by simpa [pow_two] using Nat.sqrt_le' (nthPrime n)) h

/-! ## The first few instances, unconditionally -/

/-- If `q` is prime, `p_n < q`, and no number strictly between `p_n` and `q` is prime,
then `q` is the next prime after `p_n`. -/
theorem nthPrime_succ_eq {n q : ℕ} (hq : Nat.Prime q) (hlt : nthPrime n < q)
    (hgap : ∀ m, nthPrime n < m → m < q → ¬ Nat.Prime m) : nthPrime (n + 1) = q := by
  have hle : nthPrime (n + 1) ≤ q := nthPrime_succ_le hq hlt
  rcases lt_or_eq_of_le hle with h | h
  · exact absurd (nthPrime_prime (n + 1)) (hgap _ (nthPrime_lt_nthPrime_succ n) h)
  · exact h

theorem nthPrime_zero : nthPrime 0 = 2 := Nat.nth_prime_zero_eq_two
theorem nthPrime_one : nthPrime 1 = 3 := Nat.nth_prime_one_eq_three
theorem nthPrime_two : nthPrime 2 = 5 := Nat.nth_prime_two_eq_five
theorem nthPrime_three : nthPrime 3 = 7 := Nat.nth_prime_three_eq_seven
theorem nthPrime_four : nthPrime 4 = 11 := Nat.nth_prime_four_eq_eleven

theorem nthPrime_5 : nthPrime 5 = 13 := by
  refine nthPrime_succ_eq (by norm_num) (by rw [nthPrime_four]; norm_num) ?_
  rw [nthPrime_four]
  intro m h1 h2
  interval_cases m
  norm_num

theorem nthPrime_6 : nthPrime 6 = 17 := by
  refine nthPrime_succ_eq (by norm_num) (by rw [nthPrime_5]; norm_num) ?_
  rw [nthPrime_5]
  intro m h1 h2
  interval_cases m <;> norm_num

theorem nthPrime_7 : nthPrime 7 = 19 := by
  refine nthPrime_succ_eq (by norm_num) (by rw [nthPrime_6]; norm_num) ?_
  rw [nthPrime_6]
  intro m h1 h2
  interval_cases m
  norm_num

theorem nthPrime_8 : nthPrime 8 = 23 := by
  refine nthPrime_succ_eq (by norm_num) (by rw [nthPrime_7]; norm_num) ?_
  rw [nthPrime_7]
  intro m h1 h2
  interval_cases m <;> norm_num

theorem nthPrime_9 : nthPrime 9 = 29 := by
  refine nthPrime_succ_eq (by norm_num) (by rw [nthPrime_8]; norm_num) ?_
  rw [nthPrime_8]
  intro m h1 h2
  interval_cases m <;> norm_num

theorem nthPrime_10 : nthPrime 10 = 31 := by
  refine nthPrime_succ_eq (by norm_num) (by rw [nthPrime_9]; norm_num) ?_
  rw [nthPrime_9]
  intro m h1 h2
  interval_cases m
  norm_num

theorem nthPrime_11 : nthPrime 11 = 37 := by
  refine nthPrime_succ_eq (by norm_num) (by rw [nthPrime_10]; norm_num) ?_
  rw [nthPrime_10]
  intro m h1 h2
  interval_cases m <;> norm_num

theorem nthPrime_12 : nthPrime 12 = 41 := by
  refine nthPrime_succ_eq (by norm_num) (by rw [nthPrime_11]; norm_num) ?_
  rw [nthPrime_11]
  intro m h1 h2
  interval_cases m <;> norm_num

theorem nthPrime_13 : nthPrime 13 = 43 := by
  refine nthPrime_succ_eq (by norm_num) (by rw [nthPrime_12]; norm_num) ?_
  rw [nthPrime_12]
  intro m h1 h2
  interval_cases m
  norm_num

theorem nthPrime_14 : nthPrime 14 = 47 := by
  refine nthPrime_succ_eq (by norm_num) (by rw [nthPrime_13]; norm_num) ?_
  rw [nthPrime_13]
  intro m h1 h2
  interval_cases m <;> norm_num

theorem nthPrime_15 : nthPrime 15 = 53 := by
  refine nthPrime_succ_eq (by norm_num) (by rw [nthPrime_14]; norm_num) ?_
  rw [nthPrime_14]
  intro m h1 h2
  interval_cases m <;> norm_num

theorem nthPrime_16 : nthPrime 16 = 59 := by
  refine nthPrime_succ_eq (by norm_num) (by rw [nthPrime_15]; norm_num) ?_
  rw [nthPrime_15]
  intro m h1 h2
  interval_cases m <;> norm_num

theorem nthPrime_17 : nthPrime 17 = 61 := by
  refine nthPrime_succ_eq (by norm_num) (by rw [nthPrime_16]; norm_num) ?_
  rw [nthPrime_16]
  intro m h1 h2
  interval_cases m
  norm_num

theorem nthPrime_18 : nthPrime 18 = 67 := by
  refine nthPrime_succ_eq (by norm_num) (by rw [nthPrime_17]; norm_num) ?_
  rw [nthPrime_17]
  intro m h1 h2
  interval_cases m <;> norm_num

theorem nthPrime_19 : nthPrime 19 = 71 := by
  refine nthPrime_succ_eq (by norm_num) (by rw [nthPrime_18]; norm_num) ?_
  rw [nthPrime_18]
  intro m h1 h2
  interval_cases m <;> norm_num

theorem nthPrime_20 : nthPrime 20 = 73 := by
  refine nthPrime_succ_eq (by norm_num) (by rw [nthPrime_19]; norm_num) ?_
  rw [nthPrime_19]
  intro m h1 h2
  interval_cases m
  norm_num

theorem nthPrime_21 : nthPrime 21 = 79 := by
  refine nthPrime_succ_eq (by norm_num) (by rw [nthPrime_20]; norm_num) ?_
  rw [nthPrime_20]
  intro m h1 h2
  interval_cases m <;> norm_num

theorem nthPrime_22 : nthPrime 22 = 83 := by
  refine nthPrime_succ_eq (by norm_num) (by rw [nthPrime_21]; norm_num) ?_
  rw [nthPrime_21]
  intro m h1 h2
  interval_cases m <;> norm_num

theorem nthPrime_23 : nthPrime 23 = 89 := by
  refine nthPrime_succ_eq (by norm_num) (by rw [nthPrime_22]; norm_num) ?_
  rw [nthPrime_22]
  intro m h1 h2
  interval_cases m <;> norm_num

theorem nthPrime_24 : nthPrime 24 = 97 := by
  refine nthPrime_succ_eq (by norm_num) (by rw [nthPrime_23]; norm_num) ?_
  rw [nthPrime_23]
  intro m h1 h2
  interval_cases m <;> norm_num

theorem nthPrime_25 : nthPrime 25 = 101 := by
  refine nthPrime_succ_eq (by norm_num) (by rw [nthPrime_24]; norm_num) ?_
  rw [nthPrime_24]
  intro m h1 h2
  interval_cases m <;> norm_num

/-- **Unconditional partial result.** Andrica's inequality holds for all `n ≤ 24`, i.e. for
every pair of consecutive primes up to `(97, 101)`. -/
theorem andrica_of_le_twentyfour (n : ℕ) (hn : n ≤ 24) :
    Real.sqrt (nthPrime (n + 1)) - Real.sqrt (nthPrime n) < 1 := by
  interval_cases n
  · exact andrica_of_gap_le_two_mul 0 1 (by norm_num [nthPrime_zero])
      (by norm_num [nthPrime_zero, nthPrime_one])
  · exact andrica_of_gap_le_two_mul 1 1 (by norm_num [nthPrime_one])
      (by norm_num [nthPrime_one, nthPrime_two])
  · exact andrica_of_gap_le_two_mul 2 2 (by norm_num [nthPrime_two])
      (by norm_num [nthPrime_two, nthPrime_three])
  · exact andrica_of_gap_le_two_mul 3 2 (by norm_num [nthPrime_three])
      (by norm_num [nthPrime_three, nthPrime_four])
  · exact andrica_of_gap_le_two_mul 4 3 (by norm_num [nthPrime_four])
      (by norm_num [nthPrime_four, nthPrime_5])
  · exact andrica_of_gap_le_two_mul 5 3 (by norm_num [nthPrime_5])
      (by norm_num [nthPrime_5, nthPrime_6])
  · exact andrica_of_gap_le_two_mul 6 4 (by norm_num [nthPrime_6])
      (by norm_num [nthPrime_6, nthPrime_7])
  · exact andrica_of_gap_le_two_mul 7 4 (by norm_num [nthPrime_7])
      (by norm_num [nthPrime_7, nthPrime_8])
  · exact andrica_of_gap_le_two_mul 8 4 (by norm_num [nthPrime_8])
      (by norm_num [nthPrime_8, nthPrime_9])
  · exact andrica_of_gap_le_two_mul 9 5 (by norm_num [nthPrime_9])
      (by norm_num [nthPrime_9, nthPrime_10])
  · exact andrica_of_gap_le_two_mul 10 5 (by norm_num [nthPrime_10])
      (by norm_num [nthPrime_10, nthPrime_11])
  · exact andrica_of_gap_le_two_mul 11 6 (by norm_num [nthPrime_11])
      (by norm_num [nthPrime_11, nthPrime_12])
  · exact andrica_of_gap_le_two_mul 12 6 (by norm_num [nthPrime_12])
      (by norm_num [nthPrime_12, nthPrime_13])
  · exact andrica_of_gap_le_two_mul 13 6 (by norm_num [nthPrime_13])
      (by norm_num [nthPrime_13, nthPrime_14])
  · exact andrica_of_gap_le_two_mul 14 6 (by norm_num [nthPrime_14])
      (by norm_num [nthPrime_14, nthPrime_15])
  · exact andrica_of_gap_le_two_mul 15 7 (by norm_num [nthPrime_15])
      (by norm_num [nthPrime_15, nthPrime_16])
  · exact andrica_of_gap_le_two_mul 16 7 (by norm_num [nthPrime_16])
      (by norm_num [nthPrime_16, nthPrime_17])
  · exact andrica_of_gap_le_two_mul 17 7 (by norm_num [nthPrime_17])
      (by norm_num [nthPrime_17, nthPrime_18])
  · exact andrica_of_gap_le_two_mul 18 8 (by norm_num [nthPrime_18])
      (by norm_num [nthPrime_18, nthPrime_19])
  · exact andrica_of_gap_le_two_mul 19 8 (by norm_num [nthPrime_19])
      (by norm_num [nthPrime_19, nthPrime_20])
  · exact andrica_of_gap_le_two_mul 20 8 (by norm_num [nthPrime_20])
      (by norm_num [nthPrime_20, nthPrime_21])
  · exact andrica_of_gap_le_two_mul 21 8 (by norm_num [nthPrime_21])
      (by norm_num [nthPrime_21, nthPrime_22])
  · exact andrica_of_gap_le_two_mul 22 9 (by norm_num [nthPrime_22])
      (by norm_num [nthPrime_22, nthPrime_23])
  · exact andrica_of_gap_le_two_mul 23 9 (by norm_num [nthPrime_23])
      (by norm_num [nthPrime_23, nthPrime_24])
  · exact andrica_of_gap_le_two_mul 24 9 (by norm_num [nthPrime_24])
      (by norm_num [nthPrime_24, nthPrime_25])

/-! ## Oppermann implies Andrica -/

theorem key_bound (hOpp : OppermannConjecture) (n : ℕ) :
    (nthPrime (n + 1) : ℝ) < (Real.sqrt (nthPrime n) + 1) ^ 2 := by
  set P := nthPrime n with hPdef
  set k := Nat.sqrt P with hkdef
  have hP2 : 2 ≤ P := two_le_nthPrime n
  have hk1 : 1 ≤ k := by
    have := Nat.sqrt_le_sqrt (show 1 ≤ P from le_trans (by norm_num) hP2)
    simpa using this
  have hkk : k ^ 2 ≤ P := by
    have := Nat.sqrt_le' P
    simpa [pow_two, hkdef] using this
  have hPk : P < (k + 1) ^ 2 := by
    have := Nat.lt_succ_sqrt' P
    simpa [pow_two, hkdef] using this
  have hsqrtP : (k : ℝ) ≤ Real.sqrt P := by
    rw [show (k : ℝ) = Real.sqrt ((k : ℝ) ^ 2) by
      rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hkk)
  have hsq : Real.sqrt (P : ℝ) ^ 2 = (P : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hm2 : 2 ≤ k + 1 := by omega
  rcases lt_or_ge P (k ^ 2 + k) with hcase | hcase
  · -- `P` lies in the lower half of `[k², (k+1)²)`
    obtain ⟨q, hq, hq1, hq2⟩ := (hOpp (k + 1) hm2).1
    have hlow : (k + 1) ^ 2 - (k + 1) = k ^ 2 + k := by ring_nf; omega
    rw [hlow] at hq1
    have hPq : P < q := lt_trans hcase hq1
    have hle : nthPrime (n + 1) ≤ q := nthPrime_succ_le hq hPq
    have hub : nthPrime (n + 1) ≤ k ^ 2 + 2 * k := by
      have : q < k ^ 2 + 2 * k + 1 := by
        have : (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 := by ring
        omega
      omega
    have h1 : (nthPrime (n + 1) : ℝ) ≤ (k : ℝ) ^ 2 + 2 * k := by
      exact_mod_cast (by exact_mod_cast hub : (nthPrime (n + 1) : ℝ) ≤ ((k ^ 2 + 2 * k : ℕ) : ℝ))
    have h2 : ((k : ℝ)) ^ 2 ≤ (P : ℝ) := by exact_mod_cast hkk
    nlinarith [hsqrtP, hsq, h1, h2]
  · -- `P` lies in the upper half
    obtain ⟨q, hq, hq1, hq2⟩ := (hOpp (k + 1) hm2).2
    have hPq : P < q := lt_trans hPk hq1
    have hle : nthPrime (n + 1) ≤ q := nthPrime_succ_le hq hPq
    have hub : nthPrime (n + 1) ≤ k ^ 2 + 3 * k + 1 := by
      have hexp : (k + 1) ^ 2 + (k + 1) = k ^ 2 + 3 * k + 2 := by ring
      omega
    have h1 : (nthPrime (n + 1) : ℝ) ≤ (k : ℝ) ^ 2 + 3 * k + 1 := by
      exact_mod_cast (by exact_mod_cast hub :
        (nthPrime (n + 1) : ℝ) ≤ ((k ^ 2 + 3 * k + 1 : ℕ) : ℝ))
    have hstrict : (k : ℝ) < Real.sqrt P := by
      have hlt : ((k : ℝ)) ^ 2 < (P : ℝ) := by
        have : k ^ 2 < P := by nlinarith [hk1, hcase]
        exact_mod_cast this
      nlinarith [hsqrtP, hsq, Real.sqrt_nonneg (P : ℝ)]
    have h2 : ((k : ℝ)) ^ 2 + k ≤ (P : ℝ) := by exact_mod_cast hcase
    nlinarith [hstrict, hsq, h1, h2]

/-- **Andrica's conjecture, conditional on Oppermann's conjecture.**
If between `m² - m` and `m²`, and between `m²` and `m² + m`, there is always a prime
(for `m ≥ 2`), then for all `n`, `√p_{n+1} - √p_n < 1`. -/
theorem AndricaConjecture (hOpp : OppermannConjecture) : AndricaStatement := by
  intro n
  have hpos : (0 : ℝ) < Real.sqrt (nthPrime n) + 1 := by positivity
  have h := key_bound hOpp n
  have : Real.sqrt (nthPrime (n + 1)) < Real.sqrt (nthPrime n) + 1 := by
    rw [Real.sqrt_lt' hpos]; exact h
  linarith

end Brockian.AndricaConjecture

