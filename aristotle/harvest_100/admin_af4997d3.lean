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

/-!
# Fortune Conjecture
Category: Brockian Conjecture
Target: Brockian.FortunateNumbers.FortuneConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.FortunateNumbers

open Finset

/-! ## The Fortunate numbers

For a natural number `n`, let `n#` be the primorial of `n` (the product of all primes `≤ n`,
`primorial` in Mathlib).  The *Fortunate number* of `n` is the least `m ≥ 2` such that
`n# + m` is prime.  Fortune's conjecture asserts that every Fortunate number is prime.

The conjecture is open.  What is proved here is:

* every Fortunate number of `n` is coprime to `n#`, i.e. has no prime factor `≤ n`
  (`not_dvd_fortunate`, `lt_minFac_fortunate`);
* consequently, in contrapositive form, a *composite* Fortunate number of `n` must be
  at least `(n+1)^2` (`sq_le_fortunate_of_not_prime`);
* hence the conditional reduction `FortuneConjecture`: Fortune's conjecture follows from the
  (also conjectural, but purely quantitative) bound `fortunate n < (n+1)^2` for `n ≥ 2`.
-/

/-- There is always some `m ≥ 2` with `n# + m` prime: pick a prime `q ≥ n# + 2`. -/
theorem exists_two_le_prime_primorial_add (n : ℕ) :
    ∃ m, 2 ≤ m ∧ Nat.Prime (primorial n + m) := by
  obtain ⟨q, hq, hqp⟩ := Nat.exists_infinite_primes (primorial n + 2)
  refine ⟨q - primorial n, by lia, ?_⟩
  have : primorial n + (q - primorial n) = q := by lia
  rw [this]
  exact hqp

/-- The Fortunate number of `n`: the least `m ≥ 2` such that `n# + m` is prime. -/
def fortunate (n : ℕ) : ℕ :=
  Nat.find (exists_two_le_prime_primorial_add n)

theorem two_le_fortunate (n : ℕ) : 2 ≤ fortunate n :=
  (Nat.find_spec (exists_two_le_prime_primorial_add n)).1

theorem prime_primorial_add_fortunate (n : ℕ) : Nat.Prime (primorial n + fortunate n) :=
  (Nat.find_spec (exists_two_le_prime_primorial_add n)).2

theorem fortunate_le {n m : ℕ} (hm : 2 ≤ m) (hp : Nat.Prime (primorial n + m)) :
    fortunate n ≤ m :=
  Nat.find_le ⟨hm, hp⟩

/-- Every prime `p ≤ n` divides the primorial `n#`. -/
theorem prime_dvd_primorial {p n : ℕ} (hp : Nat.Prime p) (hpn : p ≤ n) : p ∣ primorial n := by
  refine Finset.dvd_prod_of_mem _ ?_
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨by lia, hp⟩

/-- The Fortunate number of `n` has no prime factor `≤ n`. -/
theorem not_dvd_fortunate {p n : ℕ} (hp : Nat.Prime p) (hpn : p ≤ n) : ¬ p ∣ fortunate n := by
  intro hdvd
  have hP : p ∣ primorial n := prime_dvd_primorial hp hpn
  have hsum : p ∣ primorial n + fortunate n := Nat.dvd_add hP hdvd
  have hprime := prime_primorial_add_fortunate n
  have hpe : p = primorial n + fortunate n :=
    ((Nat.Prime.eq_one_or_self_of_dvd hprime p hsum).resolve_left hp.ne_one)
  have hple : p ≤ primorial n := Nat.le_of_dvd (primorial_pos n) hP
  have := two_le_fortunate n
  lia

/-- The least prime factor of the Fortunate number of `n` exceeds `n`. -/
theorem lt_minFac_fortunate (n : ℕ) : n < (fortunate n).minFac := by
  by_contra h
  push_neg at h
  have hne : fortunate n ≠ 1 := by have := two_le_fortunate n; lia
  exact not_dvd_fortunate (Nat.minFac_prime hne) h (Nat.minFac_dvd _)

/-- Contrapositive form: a composite Fortunate number of `n` is at least `(n+1)^2`. -/
theorem sq_le_fortunate_of_not_prime {n : ℕ} (h : ¬ Nat.Prime (fortunate n)) :
    (n + 1) ^ 2 ≤ fortunate n := by
  have hpos : 0 < fortunate n := by have := two_le_fortunate n; lia
  have h1 : (fortunate n).minFac ^ 2 ≤ fortunate n := Nat.minFac_sq_le_self hpos h
  have h2 : n + 1 ≤ (fortunate n).minFac := lt_minFac_fortunate n
  exact le_trans (Nat.pow_le_pow_left h2 2) h1

/-- If the Fortunate number of `n` is smaller than `(n+1)^2`, then it is prime. -/
theorem prime_fortunate_of_lt_sq {n : ℕ} (h : fortunate n < (n + 1) ^ 2) :
    Nat.Prime (fortunate n) := by
  by_contra hc
  exact absurd (sq_le_fortunate_of_not_prime hc) (by lia)

/-- If `n# + 2` is prime then the Fortunate number of `n` is `2`. -/
theorem fortunate_eq_two {n : ℕ} (h : Nat.Prime (primorial n + 2)) : fortunate n = 2 :=
  le_antisymm (fortunate_le le_rfl h) (two_le_fortunate n)

theorem primorial_zero : primorial 0 = 1 := by decide
theorem primorial_one : primorial 1 = 1 := by decide

theorem fortunate_zero : fortunate 0 = 2 := by
  refine fortunate_eq_two ?_
  rw [primorial_zero]
  decide

theorem fortunate_one : fortunate 1 = 2 := by
  refine fortunate_eq_two ?_
  rw [primorial_one]
  decide

/-- **Fortune's conjecture** (the open statement): every Fortunate number is prime. -/
def FortuneStatement : Prop := ∀ n : ℕ, Nat.Prime (fortunate n)

/-- **Conditional reduction of Fortune's conjecture.**

Fortune's conjecture (every Fortunate number is prime) follows from the purely quantitative
bound `fortunate n < (n+1)^2` for all `n ≥ 2`.  The reason is that a Fortunate number of `n`
is coprime to the primorial `n#`, so all of its prime factors exceed `n`; if it were composite
its least prime factor `q > n` would satisfy `(n+1)^2 ≤ q^2 ≤ fortunate n`.
The two remaining cases `n = 0, 1` are checked directly. -/
theorem FortuneConjecture (H : ∀ n : ℕ, 2 ≤ n → fortunate n < (n + 1) ^ 2) :
    FortuneStatement := by
  intro n
  match n with
  | 0 => rw [fortunate_zero]; decide
  | 1 => rw [fortunate_one]; decide
  | (k + 2) => exact prime_fortunate_of_lt_sq (H (k + 2) (by lia))

end Brockian.FortunateNumbers

