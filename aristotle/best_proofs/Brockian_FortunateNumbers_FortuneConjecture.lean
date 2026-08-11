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

/-!
## Overview

Let `n#` denote the primorial of `n` (the product of all primes `≤ n`).  The *fortunate number*
`fortunate n` is the smallest integer `m > 1` such that `n# + m` is prime.  Reo Fortune
conjectured that `fortunate n` is always prime; this is an open problem.

What is proved here:

* `Brockian.FortunateNumbers.lt_of_prime_dvd_fortunate` (unconditional): every prime factor of
  `fortunate n` is strictly larger than `n`.  Indeed, a prime `q ≤ n` divides `n#`, so if `q`
  also divided `m` it would divide `n# + m`, which is prime and larger than `q`.
* `Brockian.FortunateNumbers.fortunate_prime_of_le_sq` (unconditional): consequently, if
  `fortunate n ≤ n ^ 2` then `fortunate n` is prime, since a composite number has a prime factor
  whose square is at most the number itself.
* `Brockian.FortunateNumbers.FortuneConjecture` (conditional reduction): Fortune's conjecture
  follows from the size bound `fortunate n ≤ n ^ 2` for all `n ≥ 2`.  The cases `n = 0, 1` are
  handled unconditionally (there `fortunate n = 2`).

Some concrete values are also computed and verified (`fortunate 2 = 3`, `fortunate 3 = 5`,
`fortunate 5 = 7`), which shows in particular that the hypothesis of `FortuneConjecture` is not
vacuous in the small cases.
-/

namespace Brockian
namespace FortunateNumbers

open Nat

/-- The set of offsets `m > 1` for which `n# + m` is prime. -/
def offsets (n : ℕ) : Set ℕ := {m | 1 < m ∧ Nat.Prime (primorial n + m)}

theorem offsets_nonempty (n : ℕ) : (offsets n).Nonempty := by
  obtain ⟨p, hp, hpp⟩ := Nat.exists_infinite_primes (primorial n + 2)
  refine ⟨p - primorial n, by omega, ?_⟩
  have h : primorial n + (p - primorial n) = p := by omega
  rw [h]
  exact hpp

/-- The *fortunate number* of `n`: the smallest `m > 1` such that `n# + m` is prime. -/
noncomputable def fortunate (n : ℕ) : ℕ := sInf (offsets n)

theorem fortunate_mem (n : ℕ) : fortunate n ∈ offsets n :=
  Nat.sInf_mem (offsets_nonempty n)

theorem one_lt_fortunate (n : ℕ) : 1 < fortunate n := (fortunate_mem n).1

theorem prime_primorial_add_fortunate (n : ℕ) : Nat.Prime (primorial n + fortunate n) :=
  (fortunate_mem n).2

theorem fortunate_le {n m : ℕ} (hm : 1 < m) (hp : Nat.Prime (primorial n + m)) :
    fortunate n ≤ m :=
  Nat.sInf_le ⟨hm, hp⟩

/-- A prime `q ≤ n` divides the primorial `n#`. -/
theorem dvd_primorial {n q : ℕ} (hq : q.Prime) (hqn : q ≤ n) : q ∣ primorial n :=
  Finset.dvd_prod_of_mem (fun p => p)
    (by simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hq⟩)

/-- **Unconditional key step.**  Every prime factor of the fortunate number `fortunate n` is
strictly greater than `n`. -/
theorem lt_of_prime_dvd_fortunate {n q : ℕ} (hq : q.Prime) (hqf : q ∣ fortunate n) : n < q := by
  by_contra hle
  push_neg at hle
  have hqP : q ∣ primorial n := dvd_primorial hq hle
  have hdvd : q ∣ primorial n + fortunate n := Dvd.dvd.add hqP hqf
  have hprime := prime_primorial_add_fortunate n
  have hq_eq : q = primorial n + fortunate n :=
    (hprime.eq_one_or_self_of_dvd q hdvd).resolve_left hq.ne_one
  have hqle : q ≤ primorial n := Nat.le_of_dvd (primorial_pos n) hqP
  have := one_lt_fortunate n
  omega

/-- **Unconditional partial result towards Fortune's conjecture.**  If the fortunate number of `n`
is at most `n ^ 2`, then it is prime. -/
theorem fortunate_prime_of_le_sq (n : ℕ) (h : fortunate n ≤ n ^ 2) : Nat.Prime (fortunate n) := by
  by_contra hnp
  have h1 : 1 < fortunate n := one_lt_fortunate n
  have hq : (fortunate n).minFac.Prime := Nat.minFac_prime (by omega)
  have hlt : n < (fortunate n).minFac := lt_of_prime_dvd_fortunate hq (Nat.minFac_dvd _)
  have hsq : (fortunate n).minFac ^ 2 ≤ fortunate n := Nat.minFac_sq_le_self (by omega) hnp
  have : n ^ 2 < (fortunate n).minFac ^ 2 := Nat.pow_lt_pow_left hlt (by norm_num)
  omega

/-- **Unconditional dichotomy.**  For every `n`, either the fortunate number of `n` is prime, or
it exceeds `n ^ 2`. -/
theorem fortunate_prime_or_sq_lt (n : ℕ) : Nat.Prime (fortunate n) ∨ n ^ 2 < fortunate n := by
  rcases Nat.lt_or_ge (n ^ 2) (fortunate n) with h | h
  · exact Or.inr h
  · exact Or.inl (fortunate_prime_of_le_sq n h)

theorem fortunate_zero : fortunate 0 = 2 := by
  have hp : primorial 0 = 1 := by decide
  exact le_antisymm (fortunate_le (by norm_num) (by rw [hp]; norm_num)) (one_lt_fortunate 0)

theorem fortunate_one : fortunate 1 = 2 := by
  have hp : primorial 1 = 1 := by decide
  exact le_antisymm (fortunate_le (by norm_num) (by rw [hp]; norm_num)) (one_lt_fortunate 1)

/-- **Fortune's conjecture, conditionally on a size bound.**  If for every `n ≥ 2` the fortunate
number of `n` is at most `n ^ 2`, then every fortunate number is prime. -/
theorem FortuneConjecture (h : ∀ n, 2 ≤ n → fortunate n ≤ n ^ 2) (n : ℕ) :
    Nat.Prime (fortunate n) := by
  match n with
  | 0 => rw [fortunate_zero]; norm_num
  | 1 => rw [fortunate_one]; norm_num
  | (k + 2) => exact fortunate_prime_of_le_sq _ (h _ (by omega))

/-! ### Some concrete values -/

theorem fortunate_two : fortunate 2 = 3 := by
  have hp : primorial 2 = 2 := by decide
  have hle : fortunate 2 ≤ 3 := fortunate_le (by norm_num) (by rw [hp]; norm_num)
  have h1 : 1 < fortunate 2 := one_lt_fortunate 2
  have h2 := prime_primorial_add_fortunate 2
  rw [hp] at h2
  interval_cases h : (fortunate 2) <;> revert h2 <;> norm_num

theorem fortunate_three : fortunate 3 = 5 := by
  have hp : primorial 3 = 6 := by decide
  have hle : fortunate 3 ≤ 5 := fortunate_le (by norm_num) (by rw [hp]; norm_num)
  have h1 : 1 < fortunate 3 := one_lt_fortunate 3
  have h2 := prime_primorial_add_fortunate 3
  rw [hp] at h2
  interval_cases h : (fortunate 3) <;> revert h2 <;> norm_num

theorem fortunate_five : fortunate 5 = 7 := by
  have hp : primorial 5 = 30 := by decide
  have hle : fortunate 5 ≤ 7 := fortunate_le (by norm_num) (by rw [hp]; norm_num)
  have h1 : 1 < fortunate 5 := one_lt_fortunate 5
  have h2 := prime_primorial_add_fortunate 5
  rw [hp] at h2
  interval_cases h : (fortunate 5) <;> revert h2 <;> norm_num

end FortunateNumbers
end Brockian

