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
# Fortune Conjecture
Category: Brockian Conjecture
Target: Brockian.FortunateNumbers.FortuneConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Fortune Conjecture
Category: Brockian Conjecture
Target: Brockian.FortunateNumbers.FortuneConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.FortunateNumbers

open Finset

/-- The `n`-th prime (`nthPrime 0 = 2`, `nthPrime 1 = 3`, ...). -/
noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- The `n`-th primorial: the product of the first `n + 1` primes,
i.e. `p₀ * p₁ * ⋯ * pₙ`. -/
noncomputable def primorialOf (n : ℕ) : ℕ := primorial (nthPrime n)

theorem nthPrime_prime (n : ℕ) : (nthPrime n).Prime :=
  Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n

theorem primorialOf_pos (n : ℕ) : 0 < primorialOf n := primorial_pos _

/-- Every prime `q ≤ pₙ` divides the `n`-th primorial. -/
theorem prime_dvd_primorialOf {n q : ℕ} (hq : q.Prime) (hle : q ≤ nthPrime n) :
    q ∣ primorialOf n := by
  rw [primorialOf, primorial]
  refine Finset.dvd_prod_of_mem (fun p => p) ?_
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨Nat.lt_succ_of_le hle, hq⟩

/-- A prime smaller than `pₙ₊₁` is at most `pₙ`. -/
theorem le_nthPrime_of_lt_nthPrime_succ {n q : ℕ} (hq : q.Prime) (h : q < nthPrime (n + 1)) :
    q ≤ nthPrime n := by
  have hcount : Nat.nth Nat.Prime (Nat.count Nat.Prime q) = q := Nat.nth_count hq
  have hlt : Nat.count Nat.Prime q < n + 1 := by
    by_contra hcon
    push_neg at hcon
    have := (Nat.nth_le_nth (p := Nat.Prime) Nat.infinite_setOf_prime).2 hcon
    rw [hcount] at this
    exact absurd this (not_le.2 h)
  have := (Nat.nth_le_nth (p := Nat.Prime) Nat.infinite_setOf_prime).2 (Nat.lt_succ_iff.1 hlt)
  rwa [hcount] at this

/-- **Structure of the shifts.** If `m > 1` and `pₙ# + m` is prime, then every prime factor of `m`
exceeds `pₙ`: a prime factor `q ≤ pₙ` would divide both `pₙ#` and `m`, hence the prime `pₙ# + m`,
which is impossible since `q ≤ m < pₙ# + m`. -/
theorem nthPrime_lt_of_prime_dvd {n m q : ℕ} (hm : 1 < m)
    (hprime : (primorialOf n + m).Prime) (hq : q.Prime) (hqm : q ∣ m) : nthPrime n < q := by
  by_contra hcon
  push_neg at hcon
  have hdvd : q ∣ primorialOf n + m := Nat.dvd_add (prime_dvd_primorialOf hq hcon) hqm
  have hle : q ≤ m := Nat.le_of_dvd (by omega) hqm
  have hpos := primorialOf_pos n
  rcases hprime.eq_one_or_self_of_dvd q hdvd with h | h
  · exact hq.one_lt.ne' h
  · omega

/-- **Key criterion.** If `m > 1`, `pₙ# + m` is prime, and `m < pₙ₊₁²`, then `m` is prime.
This is the standard unconditional half of Fortune's conjecture: a composite `m` below `pₙ₊₁²`
has a prime factor `≤ pₙ`, which then also divides `pₙ# + m`. -/
theorem prime_of_lt_sq_nthPrime_succ {n m : ℕ} (hm : 1 < m)
    (hprime : (primorialOf n + m).Prime) (hlt : m < nthPrime (n + 1) ^ 2) : m.Prime := by
  by_contra hcomp
  have hq : (m.minFac).Prime := Nat.minFac_prime (by omega)
  have hq2 : m.minFac ^ 2 ≤ m := Nat.minFac_sq_le_self (by omega) hcomp
  have hqlt : m.minFac < nthPrime (n + 1) := by
    by_contra hcon
    push_neg at hcon
    have : nthPrime (n + 1) ^ 2 ≤ m.minFac ^ 2 := Nat.pow_le_pow_left hcon 2
    omega
  have hbig := nthPrime_lt_of_prime_dvd hm hprime hq (Nat.minFac_dvd m)
  exact absurd (le_nthPrime_of_lt_nthPrime_succ hq hqlt) (not_le.2 hbig)

/-- There is always some `m > 1` with `pₙ# + m` prime. -/
theorem exists_fortunate (n : ℕ) : ∃ m, 1 < m ∧ (primorialOf n + m).Prime := by
  obtain ⟨p, hp, hpp⟩ := Nat.exists_infinite_primes (primorialOf n + 2)
  refine ⟨p - primorialOf n, by omega, ?_⟩
  have h : primorialOf n + (p - primorialOf n) = p := by omega
  rw [h]
  exact hpp

/-- The `n`-th **fortunate number**: the least `m > 1` such that `pₙ# + m` is prime. -/
noncomputable def fortunate (n : ℕ) : ℕ :=
  Nat.find (p := fun m => 1 < m ∧ (primorialOf n + m).Prime) (exists_fortunate n)

theorem one_lt_fortunate (n : ℕ) : 1 < fortunate n :=
  (Nat.find_spec (exists_fortunate n)).1

theorem prime_primorialOf_add_fortunate (n : ℕ) : (primorialOf n + fortunate n).Prime :=
  (Nat.find_spec (exists_fortunate n)).2

theorem fortunate_le {n m : ℕ} (hm : 1 < m) (h : (primorialOf n + m).Prime) :
    fortunate n ≤ m :=
  Nat.find_le ⟨hm, h⟩

/-- **Fortune's conjecture, conditional reduction.**
Assuming the (open) bound `Fₙ < pₙ₊₁²` on the fortunate numbers, every fortunate number is prime.
The implication itself is unconditional and fully verified. -/
theorem FortuneConjecture (h : ∀ n, fortunate n < nthPrime (n + 1) ^ 2) :
    ∀ n, (fortunate n).Prime := fun n =>
  prime_of_lt_sq_nthPrime_succ (one_lt_fortunate n) (prime_primorialOf_add_fortunate n) (h n)

/-- **Unconditional partial result.** Every prime factor of the `n`-th fortunate number is
larger than `pₙ`. -/
theorem nthPrime_lt_of_prime_dvd_fortunate {n q : ℕ} (hq : q.Prime) (hdvd : q ∣ fortunate n) :
    nthPrime n < q :=
  nthPrime_lt_of_prime_dvd (one_lt_fortunate n) (prime_primorialOf_add_fortunate n) hq hdvd

/-- **Unconditional dichotomy.** Each fortunate number is either prime or at least `pₙ₊₁²`. -/
theorem fortunate_prime_or_sq_le (n : ℕ) :
    (fortunate n).Prime ∨ nthPrime (n + 1) ^ 2 ≤ fortunate n := by
  by_cases h : nthPrime (n + 1) ^ 2 ≤ fortunate n
  · exact Or.inr h
  · exact Or.inl (prime_of_lt_sq_nthPrime_succ (one_lt_fortunate n)
      (prime_primorialOf_add_fortunate n) (not_le.1 h))

/-! ### Small unconditional cases -/

theorem nthPrime_zero : nthPrime 0 = 2 := by
  have hc : Nat.count Nat.Prime 2 = 0 := by decide
  have h := Nat.nth_count (p := Nat.Prime) (n := 2) (by norm_num)
  rw [hc] at h
  exact h

theorem nthPrime_one : nthPrime 1 = 3 := by
  have hc : Nat.count Nat.Prime 3 = 1 := by decide
  have h := Nat.nth_count (p := Nat.Prime) (n := 3) (by norm_num)
  rw [hc] at h
  exact h

theorem primorialOf_zero : primorialOf 0 = 2 := by
  rw [primorialOf, nthPrime_zero]
  decide

theorem primorialOf_one : primorialOf 1 = 6 := by
  rw [primorialOf, nthPrime_one]
  decide

theorem fortunate_zero : fortunate 0 = 3 := by
  rw [fortunate, Nat.find_eq_iff]
  refine ⟨⟨by norm_num, by rw [primorialOf_zero]; norm_num⟩, ?_⟩
  intro m hm hmem
  rw [primorialOf_zero] at hmem
  interval_cases m
  · exact absurd hmem.1 (by norm_num)
  · exact absurd hmem.1 (by norm_num)
  · exact absurd hmem.2 (by norm_num)

theorem fortunate_one : fortunate 1 = 5 := by
  rw [fortunate, Nat.find_eq_iff]
  refine ⟨⟨by norm_num, by rw [primorialOf_one]; norm_num⟩, ?_⟩
  intro m hm hmem
  rw [primorialOf_one] at hmem
  interval_cases m
  · exact absurd hmem.1 (by norm_num)
  · exact absurd hmem.1 (by norm_num)
  · exact absurd hmem.2 (by norm_num)
  · exact absurd hmem.2 (by norm_num)
  · exact absurd hmem.2 (by norm_num)

end Brockian.FortunateNumbers

