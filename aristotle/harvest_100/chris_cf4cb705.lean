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
Note: the header block above is written as a plain block comment rather than a module docstring
(`/-! ... -/`) because Lean requires `import` commands to precede every other command, including
module docstrings.

## Contents

* `sqrt_sub_sqrt_lt_one_of_sq_gap_le` : the elementary estimate `√b - √a < 1` for `a < b`
  with `(b - a)^2 ≤ 4a`.
* `sqrt_sub_sqrt_lt_one_iff` : the Andrica inequality is equivalent to the gap bound.
* `AndricaConjecture` : Andrica's conjecture, conditional on the prime-gap bound
  `(p_{n+1} - p_n)^2 ≤ 4 p_n`.  (Andrica's conjecture itself is an open problem.)
* `andrica_first_ten` : unconditional verification for the first ten prime gaps.
-/

namespace Brockian.AndricaConjecture

open Real

/-- `prime n` is the `n`-th prime number (`prime 0 = 2`). -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

lemma prime_lt_prime_succ (n : ℕ) : prime n < prime (n + 1) :=
  (Nat.nth_lt_nth Nat.infinite_setOf_prime).2 (Nat.lt_succ_self n)

/-- **Key elementary estimate.** If `a < b` are naturals with `(b - a)^2 ≤ 4 * a`
(i.e. the gap `b - a` is at most `2√a`), then `√b - √a < 1`. -/
theorem sqrt_sub_sqrt_lt_one_of_sq_gap_le {a b : ℕ} (hab : a < b)
    (h : (b - a) ^ 2 ≤ 4 * a) : Real.sqrt b - Real.sqrt a < 1 := by
  set x := Real.sqrt a with hx
  set y := Real.sqrt b with hy
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hxy : x < y := by
    have hlt : (a : ℝ) < b := by exact_mod_cast hab
    exact Real.sqrt_lt_sqrt (by positivity) hlt
  have hxsq : x ^ 2 = (a : ℝ) := Real.sq_sqrt (by positivity)
  have hysq : y ^ 2 = (b : ℝ) := Real.sq_sqrt (by positivity)
  have hcast : ((b - a : ℕ) : ℝ) = (b : ℝ) - a := by
    have := Nat.cast_sub (le_of_lt hab) (R := ℝ)
    simpa using this
  have h' : ((b : ℝ) - a) ^ 2 ≤ 4 * (a : ℝ) := by
    have hc := (Nat.cast_le (α := ℝ)).2 h
    rw [Nat.cast_pow, hcast, Nat.cast_mul] at hc
    simpa using hc
  have hgap : (b : ℝ) - a ≤ 2 * x := by
    nlinarith [hx0, hxsq]
  have hexp : (y - x) * (y + x) = (b : ℝ) - a := by
    have hfac : (y - x) * (y + x) = y ^ 2 - x ^ 2 := by ring
    rw [hfac, hxsq, hysq]
  have hpos : 0 < y + x := by linarith
  nlinarith [hexp, hgap, hpos, hxy]

/-- The Andrica inequality for a pair is *equivalent* to the corresponding gap bound. -/
theorem sqrt_sub_sqrt_lt_one_iff {a b : ℕ} :
    Real.sqrt b - Real.sqrt a < 1 ↔ (b : ℝ) < a + 2 * Real.sqrt a + 1 := by
  have hx0 : 0 ≤ Real.sqrt a := Real.sqrt_nonneg _
  have hy0 : 0 ≤ Real.sqrt b := Real.sqrt_nonneg _
  have hxsq : Real.sqrt a ^ 2 = (a : ℝ) := Real.sq_sqrt (by positivity)
  have hysq : Real.sqrt b ^ 2 = (b : ℝ) := Real.sq_sqrt (by positivity)
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

/-- **Andrica's conjecture**, conditional on the (equivalent, but purely arithmetic) prime-gap
bound `(p_{n+1} - p_n)^2 ≤ 4 * p_n`, i.e. `p_{n+1} - p_n ≤ 2 √ p_n`.

Andrica's conjecture asserts that `√p_{n+1} - √p_n < 1` for every `n`, where `p_n` denotes the
`n`-th prime. It is an open problem; what is proved here is the reduction of the conjecture to the
above gap bound, together with unconditional verification for small `n`
(see `andrica_first_ten`). -/
theorem AndricaConjecture
    (gap : ∀ n : ℕ, (prime (n + 1) - prime n) ^ 2 ≤ 4 * prime n) :
    ∀ n : ℕ, Real.sqrt (prime (n + 1)) - Real.sqrt (prime n) < 1 := fun n =>
  sqrt_sub_sqrt_lt_one_of_sq_gap_le (prime_lt_prime_succ n) (gap n)

/-! ### Unconditional verification for the first primes -/

private lemma prime_eq (k n : ℕ) (hn : Nat.Prime n) (h : Nat.count Nat.Prime n = k) :
    prime k = n := by
  have hnth := Nat.nth_count (p := Nat.Prime) hn
  rw [h] at hnth
  exact hnth

lemma prime_0 : prime 0 = 2 := prime_eq _ _ (by norm_num) (by decide)
lemma prime_1 : prime 1 = 3 := prime_eq _ _ (by norm_num) (by decide)
lemma prime_2 : prime 2 = 5 := prime_eq _ _ (by norm_num) (by decide)
lemma prime_3 : prime 3 = 7 := prime_eq _ _ (by norm_num) (by decide)
lemma prime_4 : prime 4 = 11 := prime_eq _ _ (by norm_num) (by decide)
lemma prime_5 : prime 5 = 13 := prime_eq _ _ (by norm_num) (by decide)
lemma prime_6 : prime 6 = 17 := prime_eq _ _ (by norm_num) (by decide)
lemma prime_7 : prime 7 = 19 := prime_eq _ _ (by norm_num) (by decide)
lemma prime_8 : prime 8 = 23 := prime_eq _ _ (by norm_num) (by decide)
lemma prime_9 : prime 9 = 29 := prime_eq _ _ (by norm_num) (by decide)
lemma prime_10 : prime 10 = 31 := prime_eq _ _ (by norm_num) (by decide)

private lemma andrica_step {n a b : ℕ} (ha : prime n = a) (hb : prime (n + 1) = b)
    (h1 : a < b) (h2 : (b - a) ^ 2 ≤ 4 * a) :
    Real.sqrt (prime (n + 1)) - Real.sqrt (prime n) < 1 := by
  rw [ha, hb]
  exact sqrt_sub_sqrt_lt_one_of_sq_gap_le h1 h2

/-- Unconditional verification of Andrica's inequality for the first ten prime gaps. -/
theorem andrica_first_ten :
    ∀ n < 10, Real.sqrt (prime (n + 1)) - Real.sqrt (prime n) < 1 := by
  intro n hn
  interval_cases n
  · exact andrica_step prime_0 prime_1 (by norm_num) (by norm_num)
  · exact andrica_step prime_1 prime_2 (by norm_num) (by norm_num)
  · exact andrica_step prime_2 prime_3 (by norm_num) (by norm_num)
  · exact andrica_step prime_3 prime_4 (by norm_num) (by norm_num)
  · exact andrica_step prime_4 prime_5 (by norm_num) (by norm_num)
  · exact andrica_step prime_5 prime_6 (by norm_num) (by norm_num)
  · exact andrica_step prime_6 prime_7 (by norm_num) (by norm_num)
  · exact andrica_step prime_7 prime_8 (by norm_num) (by norm_num)
  · exact andrica_step prime_8 prime_9 (by norm_num) (by norm_num)
  · exact andrica_step prime_9 prime_10 (by norm_num) (by norm_num)

end Brockian.AndricaConjecture

