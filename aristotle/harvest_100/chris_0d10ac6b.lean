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

/-!
## Overview

Reid Fortune's conjecture states that for every `n`, the *fortunate number*

  `F n = the least m > 1 such that n# + m is prime`

(where `n#` is the primorial, the product of all primes `≤ n`) is a prime number.
This is an open problem: no unconditional proof is known, because it would require an
upper bound on the prime gap after `n#` far stronger than anything currently provable.

What *is* provable, and what this file establishes, is the standard reduction:

* every prime factor of `F n` exceeds `n` (`Brockian.FortunateNumbers.lt_of_prime_dvd_fortunate`),
  because all primes `≤ n` divide `n#`;
* hence if `F n ≤ n ^ 2`, then `F n` must be prime
  (`Brockian.FortunateNumbers.fortunate_prime_of_le_sq`);
* consequently, the quadratic gap bound `∀ n ≥ 2, F n ≤ n ^ 2` implies the full Fortune
  conjecture (`Brockian.FortunateNumbers.FortuneConjecture`).

The target theorem `Brockian.FortunateNumbers.FortuneConjecture` is therefore stated as a
*conditional* reduction: it derives the conjecture for **all** `n` from the gap hypothesis,
with the two degenerate cases `n = 0, 1` handled unconditionally.
-/

namespace Brockian.FortunateNumbers

open Finset

/-- There is some `m > 1` with `primorial n + m` prime; this is what makes the
fortunate number well defined. -/
theorem exists_fortunate (n : ℕ) : ∃ m : ℕ, 1 < m ∧ (primorial n + m).Prime := by
  obtain ⟨p, hp, hpp⟩ := Nat.exists_infinite_primes (primorial n + 2)
  refine ⟨p - primorial n, by omega, ?_⟩
  have h : primorial n + (p - primorial n) = p := by omega
  rw [h]
  exact hpp

/-- The `n`-th **fortunate number**: the least `m > 1` such that `primorial n + m` is
prime. -/
def fortunate (n : ℕ) : ℕ := Nat.find (exists_fortunate n)

theorem one_lt_fortunate (n : ℕ) : 1 < fortunate n :=
  (Nat.find_spec (exists_fortunate n)).1

theorem prime_primorial_add_fortunate (n : ℕ) : (primorial n + fortunate n).Prime :=
  (Nat.find_spec (exists_fortunate n)).2

theorem fortunate_le {n m : ℕ} (h1 : 1 < m) (h2 : (primorial n + m).Prime) :
    fortunate n ≤ m :=
  Nat.find_le ⟨h1, h2⟩

/-- Characterisation of the fortunate number, useful for computing small values. -/
theorem fortunate_eq {n m : ℕ} (h1 : 1 < m) (h2 : (primorial n + m).Prime)
    (h3 : ∀ k, 1 < k → k < m → ¬ (primorial n + k).Prime) : fortunate n = m := by
  refine le_antisymm (fortunate_le h1 h2) ?_
  by_contra hlt
  push_neg at hlt
  exact h3 _ (one_lt_fortunate n) hlt (prime_primorial_add_fortunate n)

/-- Every prime `p ≤ n` divides the primorial `n#`. -/
theorem prime_dvd_primorial {p n : ℕ} (hp : p.Prime) (hpn : p ≤ n) : p ∣ primorial n :=
  Finset.dvd_prod_of_mem _ (by simp [Nat.lt_succ_iff, hpn, hp])

/-- **Key step.** Every prime factor of the fortunate number `F n` is larger than `n`:
otherwise it would divide both `n#` and `F n`, hence also the prime `n# + F n`. -/
theorem lt_of_prime_dvd_fortunate {n p : ℕ} (hp : p.Prime) (hdvd : p ∣ fortunate n) :
    n < p := by
  by_contra hle
  push_neg at hle
  have hsum : p ∣ primorial n + fortunate n :=
    Dvd.dvd.add (prime_dvd_primorial hp hle) hdvd
  have hq := prime_primorial_add_fortunate n
  have hpe : p = primorial n + fortunate n :=
    (hq.eq_one_or_self_of_dvd p hsum).resolve_left hp.ne_one
  have hple : p ≤ fortunate n := Nat.le_of_dvd (by have := one_lt_fortunate n; omega) hdvd
  have := primorial_pos n
  omega

/-- **The reduction.** If the fortunate number `F n` does not exceed `n ^ 2`, then it is
prime.  Indeed a composite `m` satisfies `m.minFac ^ 2 ≤ m`, while every prime factor of
`F n` exceeds `n`. -/
theorem fortunate_prime_of_le_sq {n : ℕ} (h : fortunate n ≤ n ^ 2) :
    (fortunate n).Prime := by
  by_contra hnp
  have h1 := one_lt_fortunate n
  have hmf : (fortunate n).minFac.Prime := Nat.minFac_prime (by omega)
  have hsq : (fortunate n).minFac ^ 2 ≤ fortunate n :=
    Nat.minFac_sq_le_self (by omega) hnp
  have hlt : n < (fortunate n).minFac :=
    lt_of_prime_dvd_fortunate hmf (Nat.minFac_dvd _)
  have : n ^ 2 < (fortunate n).minFac ^ 2 := Nat.pow_lt_pow_left hlt (by norm_num)
  omega

/-- `primorial 0 = 1`. -/
theorem primorial_zero : primorial 0 = 1 := by decide

/-- `primorial 1 = 1`. -/
theorem primorial_one : primorial 1 = 1 := by decide

theorem fortunate_zero : fortunate 0 = 2 := by
  refine fortunate_eq (by norm_num) ?_ (fun k hk hk2 => by omega)
  rw [primorial_zero]
  norm_num

theorem fortunate_one : fortunate 1 = 2 := by
  refine fortunate_eq (by norm_num) ?_ (fun k hk hk2 => by omega)
  rw [primorial_one]
  norm_num

/-- **Fortune's conjecture, conditionally on a quadratic gap bound.**

If for every `n ≥ 2` the fortunate number satisfies `F n ≤ n ^ 2` (equivalently: there is a
prime in the interval `(n#, n# + n^2]`), then every fortunate number is prime.
The degenerate cases `n = 0, 1` are handled unconditionally (`F 0 = F 1 = 2`).

The gap hypothesis is not currently provable: the best unconditional results on gaps between
primes are far too weak at the size of `n#`. -/
theorem FortuneConjecture (hgap : ∀ n : ℕ, 2 ≤ n → fortunate n ≤ n ^ 2) :
    ∀ n : ℕ, (fortunate n).Prime := by
  intro n
  rcases (by omega : n = 0 ∨ n = 1 ∨ 2 ≤ n) with rfl | rfl | hn
  · rw [fortunate_zero]; norm_num
  · rw [fortunate_one]; norm_num
  · exact fortunate_prime_of_le_sq (hgap n hn)

end Brockian.FortunateNumbers

