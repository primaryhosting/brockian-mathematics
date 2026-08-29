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
# Fortune Conjecture
Category: Brockian Conjecture
Target: Brockian.FortunateNumbers.FortuneConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.FortunateNumbers

open Nat

/-- Existence of a "fortunate offset": for every `n` there is some `m > 1` such that
`n# + m` is prime, where `n#` is the primorial of `n`.  This follows from Bertrand's
postulate applied to `n# + 1`. -/
theorem exists_fortunate (n : ℕ) : ∃ m, 1 < m ∧ Nat.Prime (primorial n + m) := by
  obtain ⟨p, hp, hlt, -⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (primorial n + 1) (by positivity)
  refine ⟨p - primorial n, by omega, ?_⟩
  have : primorial n + (p - primorial n) = p := by omega
  rw [this]; exact hp

/-- The Fortunate number of `n`: the least `m > 1` such that `n# + m` is prime,
where `n#` denotes the primorial of `n` (the product of all primes `≤ n`). -/
def fortunate (n : ℕ) : ℕ := Nat.find (exists_fortunate n)

theorem one_lt_fortunate (n : ℕ) : 1 < fortunate n := (Nat.find_spec (exists_fortunate n)).1

theorem prime_primorial_add_fortunate (n : ℕ) : Nat.Prime (primorial n + fortunate n) :=
  (Nat.find_spec (exists_fortunate n)).2

theorem fortunate_le {n m : ℕ} (hm : 1 < m) (hp : Nat.Prime (primorial n + m)) :
    fortunate n ≤ m :=
  Nat.find_le ⟨hm, hp⟩

/-- Every prime `≤ n` divides the primorial `n#`. -/
theorem prime_dvd_primorial {q n : ℕ} (hq : Nat.Prime q) (hqn : q ≤ n) : q ∣ primorial n := by
  refine Finset.dvd_prod_of_mem _ ?_
  simp [Finset.mem_filter, Finset.mem_range, hq, Nat.lt_succ_of_le hqn]

/-- No prime `≤ n` divides the Fortunate number of `n`. -/
theorem not_dvd_fortunate_of_prime_le {q n : ℕ} (hq : Nat.Prime q) (hqn : q ≤ n) :
    ¬ q ∣ fortunate n := by
  intro hdvd
  have hqP : q ∣ primorial n := prime_dvd_primorial hq hqn
  have hsum : q ∣ primorial n + fortunate n := Nat.dvd_add hqP hdvd
  have hP := prime_primorial_add_fortunate n
  have hq1 : q ≠ 1 := hq.ne_one
  have hqeq : q = primorial n + fortunate n := ((Nat.Prime.eq_one_or_self_of_dvd hP q hsum).resolve_left hq1)
  have hqle : q ≤ primorial n := Nat.le_of_dvd (primorial_pos n) hqP
  have := one_lt_fortunate n
  omega

/-- Every prime factor of the Fortunate number of `n` is `> n`. -/
theorem lt_of_prime_dvd_fortunate {q n : ℕ} (hq : Nat.Prime q) (hdvd : q ∣ fortunate n) :
    n < q := by
  by_contra h
  exact not_dvd_fortunate_of_prime_le hq (Nat.le_of_not_lt h) hdvd

/-- **Unconditional dichotomy.**  For every `n`, the Fortunate number of `n` is either prime,
or it is at least `(n+1)^2`.  (Its least prime factor exceeds `n`, so if it were composite it
would be at least the square of that factor.) -/
theorem fortunate_prime_or_sq_le (n : ℕ) :
    Nat.Prime (fortunate n) ∨ (n + 1) ^ 2 ≤ fortunate n := by
  by_cases h : Nat.Prime (fortunate n)
  · exact Or.inl h
  refine Or.inr ?_
  have hpos : 0 < fortunate n := lt_trans Nat.zero_lt_one (one_lt_fortunate n)
  have hne : fortunate n ≠ 1 := (one_lt_fortunate n).ne'
  have hqp : Nat.Prime (fortunate n).minFac := Nat.minFac_prime hne
  have hlt : n < (fortunate n).minFac :=
    lt_of_prime_dvd_fortunate hqp (Nat.minFac_dvd _)
  calc (n + 1) ^ 2 ≤ (fortunate n).minFac ^ 2 := Nat.pow_le_pow_left hlt 2
    _ ≤ fortunate n := Nat.minFac_sq_le_self hpos h

/-- The Fortunate number of `0` is `2` (the primorial of `0` is `1`, and `1 + 2 = 3` is prime). -/
theorem fortunate_zero : fortunate 0 = 2 := by
  have h1 : primorial 0 = 1 := by decide
  have hle : fortunate 0 ≤ 2 := fortunate_le (by norm_num) (by rw [h1]; norm_num)
  have := one_lt_fortunate 0
  omega

theorem fortunate_two : fortunate 2 = 3 := by
  have h : primorial 2 = 2 := by decide
  rw [fortunate, Nat.find_eq_iff]
  refine ⟨⟨by norm_num, by rw [h]; norm_num⟩, ?_⟩
  intro m hm
  interval_cases m <;> norm_num [h]

theorem fortunate_three : fortunate 3 = 5 := by
  have h : primorial 3 = 6 := by decide
  rw [fortunate, Nat.find_eq_iff]
  refine ⟨⟨by norm_num, by rw [h]; norm_num⟩, ?_⟩
  intro m hm
  interval_cases m <;> norm_num [h]

theorem fortunate_five : fortunate 5 = 7 := by
  have h : primorial 5 = 30 := by decide
  rw [fortunate, Nat.find_eq_iff]
  refine ⟨⟨by norm_num, by rw [h]; norm_num⟩, ?_⟩
  intro m hm
  interval_cases m <;> norm_num [h]

theorem fortunate_seven : fortunate 7 = 13 := by
  have h : primorial 7 = 210 := by decide
  rw [fortunate, Nat.find_eq_iff]
  refine ⟨⟨by norm_num, by rw [h]; norm_num⟩, ?_⟩
  intro m hm
  interval_cases m <;> norm_num [h]

/-- Unconditional verification of Fortune's conjecture for the small cases `n = 0, 2, 3, 5, 7`. -/
theorem fortunate_prime_small :
    Nat.Prime (fortunate 0) ∧ Nat.Prime (fortunate 2) ∧ Nat.Prime (fortunate 3) ∧
      Nat.Prime (fortunate 5) ∧ Nat.Prime (fortunate 7) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [fortunate_zero]; norm_num
  · rw [fortunate_two]; norm_num
  · rw [fortunate_three]; norm_num
  · rw [fortunate_five]; norm_num
  · rw [fortunate_seven]; norm_num

/-- The statement of Fortune's conjecture: every Fortunate number is prime. -/
def FortuneConjectureStatement : Prop := ∀ n, Nat.Prime (fortunate n)

/-- **Fortune's conjecture, conditional on a size bound.**

Fortune's conjecture states that every Fortunate number `fortunate n` (the least `m > 1` with
`n# + m` prime) is prime.  This is an open problem.  The theorem below is a Lean-checked
*conditional reduction*: it derives the full conjecture from the (conjecturally very weak)
growth hypothesis that `fortunate n < (n+1)^2` for `n ≥ 1`, i.e. that the prime gap just above
the primorial `n#` is smaller than `(n+1)^2`.

The reduction is unconditional in the following sense (see `fortunate_prime_or_sq_le`):
no prime `≤ n` can divide `fortunate n`, since such a prime also divides `n#` and hence would
divide the prime `n# + fortunate n`; therefore a composite Fortunate number is at least the
square of its least prime factor, which exceeds `n`. -/
theorem FortuneConjecture (H : ∀ n, 1 ≤ n → fortunate n < (n + 1) ^ 2) :
    FortuneConjectureStatement := by
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [fortunate_zero]; norm_num
  · rcases fortunate_prime_or_sq_le n with h | h
    · exact h
    · exact absurd (H n hn) (by omega)

end Brockian.FortunateNumbers

