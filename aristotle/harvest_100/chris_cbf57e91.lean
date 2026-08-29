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

/-- `IsFortunate n m` says that `m` is the *fortunate number* attached to the primorial `n#`:
it is the least integer `m > 1` such that `n# + m` is prime. -/
def IsFortunate (n m : ℕ) : Prop :=
  IsLeast {k : ℕ | 1 < k ∧ Nat.Prime (primorial n + k)} m

/-- Fortunate numbers exist: for every `n` there is a least `m > 1` with `n# + m` prime. -/
theorem exists_fortunate (n : ℕ) : ∃ m, IsFortunate n m := by
  have hne : {k : ℕ | 1 < k ∧ Nat.Prime (primorial n + k)}.Nonempty := by
    obtain ⟨p, hp1, hp⟩ := Nat.exists_infinite_primes (primorial n + 2)
    refine ⟨p - primorial n, by omega, ?_⟩
    rwa [Nat.add_sub_cancel' (by omega : primorial n ≤ p)]
  exact ⟨_, Nat.sInf_mem hne, fun _ hk => Nat.sInf_le hk⟩

/-- **Unconditional structure result.** If `m > 1` and `n# + m` is prime, then no prime `q ≤ n`
divides `m`; i.e. every prime factor of `m` exceeds `n`.  (In particular a fortunate number is
coprime to `n#`.) -/
theorem not_dvd_of_prime_le {n m q : ℕ} (hm1 : 1 < m) (hp : Nat.Prime (primorial n + m))
    (hq : Nat.Prime q) (hqn : q ≤ n) : ¬ q ∣ m := by
  intro hdvdm
  have hdvdN : q ∣ primorial n :=
    Finset.dvd_prod_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hq⟩)
  have hdvd : q ∣ primorial n + m := Nat.dvd_add hdvdN hdvdm
  have hle' : q ≤ m := Nat.le_of_dvd (by omega) hdvdm
  have hpos : 0 < primorial n := primorial_pos n
  rcases Nat.Prime.eq_one_or_self_of_dvd hp _ hdvd with h | h
  · exact hq.one_lt.ne' h
  · omega

/-- **Key unconditional step.** If `m > 1`, `n# + m` is prime and `m ≤ n ^ 2`, then `m` is prime.

Indeed, a composite `m` would have a prime factor `q` with `q ^ 2 ≤ m ≤ n ^ 2`, hence `q ≤ n`,
so `q` divides the primorial `n#` as well as `m`, hence divides the prime `n# + m`, which is
impossible since `1 < q < n# + m`. -/
theorem prime_of_prime_primorial_add_of_le_sq {n m : ℕ} (hm1 : 1 < m)
    (hp : Nat.Prime (primorial n + m)) (hle : m ≤ n ^ 2) : Nat.Prime m := by
  by_contra hmp
  have hqp : Nat.Prime m.minFac := Nat.minFac_prime (by omega)
  have hq2 : m.minFac ^ 2 ≤ m := Nat.minFac_sq_le_self (by omega) hmp
  have hqn : m.minFac ≤ n := by
    by_contra hc
    have : n ^ 2 < m.minFac ^ 2 := Nat.pow_lt_pow_left (by omega) (by norm_num)
    omega
  exact not_dvd_of_prime_le hm1 hp hqp hqn (Nat.minFac_dvd m)

/-- A sharper version of `prime_of_prime_primorial_add_of_le_sq`: it suffices that `m < r ^ 2`
where `r` is any prime with the property that there is no prime in the interval `(n, r)`
(e.g. `r` the least prime exceeding `n`). -/
theorem prime_of_prime_primorial_add_of_lt_sq {n m r : ℕ} (hm1 : 1 < m)
    (hp : Nat.Prime (primorial n + m)) (hgap : ∀ q : ℕ, Nat.Prime q → n < q → r ≤ q)
    (hlt : m < r ^ 2) : Nat.Prime m := by
  by_contra hmp
  have hqp : Nat.Prime m.minFac := Nat.minFac_prime (by omega)
  have hq2 : m.minFac ^ 2 ≤ m := Nat.minFac_sq_le_self (by omega) hmp
  have hqn : m.minFac ≤ n := by
    by_contra hc
    have : r ≤ m.minFac := hgap _ hqp (by omega)
    have : r ^ 2 ≤ m.minFac ^ 2 := Nat.pow_le_pow_left this 2
    omega
  exact not_dvd_of_prime_le hm1 hp hqp hqn (Nat.minFac_dvd m)

/-- **Fortune's conjecture, conditional reduction.**

Fortune's conjecture states that every fortunate number is prime; it is open.  The statement
below reduces it to the size bound saying that the fortunate number attached to `n#` is at
most `n ^ 2`.  (Fortunate numbers are conjecturally of size `O((log n)^2)`, far below `n ^ 2`,
so `hgap` is a very weak form of the expected prime-gap behaviour after primorials.) -/
theorem FortuneConjecture (hgap : ∀ n m : ℕ, IsFortunate n m → m ≤ n ^ 2) :
    ∀ n m : ℕ, IsFortunate n m → Nat.Prime m := fun n m hm =>
  prime_of_prime_primorial_add_of_le_sq hm.1.1 hm.1.2 (hgap n m hm)

/-- Sharper conditional form of Fortune's conjecture: it is enough to know that the fortunate
number attached to `n#` is smaller than the square of the least prime exceeding `n`. -/
theorem fortuneConjecture_of_lt_next_prime_sq
    (hgap : ∀ n m r : ℕ, IsFortunate n m → (∀ q : ℕ, Nat.Prime q → n < q → r ≤ q) → m < r ^ 2) :
    ∀ n m : ℕ, IsFortunate n m → Nat.Prime m := by
  intro n m hm
  obtain ⟨r, -, hrmin⟩ : ∃ r : ℕ, Nat.Prime r ∧ ∀ q : ℕ, Nat.Prime q → n < q → r ≤ q := by
    have hne : {q : ℕ | Nat.Prime q ∧ n < q}.Nonempty := by
      obtain ⟨p, hp1, hp⟩ := Nat.exists_infinite_primes (n + 1)
      exact ⟨p, hp, by omega⟩
    obtain ⟨hr1, -⟩ := Nat.sInf_mem hne
    exact ⟨_, hr1, fun q hq hqn => Nat.sInf_le ⟨hq, hqn⟩⟩
  exact prime_of_prime_primorial_add_of_lt_sq hm.1.1 hm.1.2 hrmin (hgap n m r hm hrmin)

/-- Unconditional instance: the fortunate number attached to `7# = 210` is `13`, which is prime. -/
theorem isFortunate_seven : IsFortunate 7 13 := by
  have h210 : primorial 7 = 210 := by decide
  constructor
  · refine ⟨by norm_num, ?_⟩
    rw [h210]; norm_num
  · rintro k ⟨hk1, hk2⟩
    rw [h210] at hk2
    by_contra hc
    interval_cases k <;> revert hk2 <;> norm_num

end Brockian.FortunateNumbers

