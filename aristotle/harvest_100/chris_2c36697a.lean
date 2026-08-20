import Mathlib
import RequestProject.GoldbachWheelK2_727

/-!
# Goldbach Wheel K 2 727 — Mathlib restatement

The target theorem `Brockian.GoldbachWheelK2_727` is stated in a self-contained way (its own
primality predicate `Brockian.IsPrime`), because the required file header must be the very first
thing in that file and Lean does not accept `import` after it.  Here we bridge that predicate to
`Nat.Prime` and restate the result in Mathlib terms.
-/

namespace Brockian

theorem nat_prime_iff_isPrime {p : ℕ} : Nat.Prime p ↔ IsPrime p :=
  Nat.prime_def

/-- Mathlib restatement: every even `n` with `4 ≤ n ≤ 727` is a sum of two primes. -/
theorem GoldbachWheelK2_727_natPrime (n : ℕ) (h4 : 4 ≤ n) (h727 : n ≤ 727) (hev : Even n) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  obtain ⟨p, q, hp, hq, hpq⟩ := GoldbachWheelK2_727 n h4 h727 (Nat.even_iff.mp hev)
  exact ⟨p, q, nat_prime_iff_isPrime.mpr hp, nat_prime_iff_isPrime.mpr hq, hpq⟩

end Brockian

/-!
# Goldbach Wheel K 2 727
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_727
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- Primality of a natural number, in the usual sense: `p` is at least `2` and its only
divisors are `1` and `p`. -/
def IsPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ m : Nat, m ∣ p → m = 1 ∨ m = p

/-- The `K = 2` Goldbach property: `n` is a sum of two primes. -/
def GoldbachK2 (n : Nat) : Prop :=
  ∃ p q : Nat, IsPrime p ∧ IsPrime q ∧ p + q = n

/-- `noDivIn p k` is `true` when no `m` with `2 ≤ m ≤ k` divides `p`. -/
def noDivIn (p : Nat) : Nat → Bool
  | 0 => true
  | 1 => true
  | (k + 2) => (p % (k + 2) != 0) && noDivIn p (k + 1)

/-- A Boolean primality test by trial division. -/
def isPrimeB (p : Nat) : Bool :=
  2 ≤ p && noDivIn p (p - 1)

theorem noDivIn_spec (p : Nat) :
    ∀ k, noDivIn p k = true → ∀ m, 2 ≤ m → m ≤ k → p % m ≠ 0 := by
  intro k
  induction k with
  | zero => intro _ m hm hmk; omega
  | succ k ih =>
    match k with
    | 0 => intro _ m hm hmk; omega
    | k + 1 =>
      intro h m hm hmk
      rw [noDivIn] at h
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      rcases Nat.lt_or_ge m (k + 2) with hlt | hge
      · exact ih h.2 m hm (by omega)
      · have hmeq : m = k + 2 := by omega
        subst hmeq
        exact h.1

/-- The Boolean test is sound. -/
theorem isPrime_of_isPrimeB {p : Nat} (h : isPrimeB p = true) : IsPrime p := by
  rw [isPrimeB] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h2, hnd⟩ := h
  refine ⟨h2, ?_⟩
  intro m hm
  by_cases hm0 : m = 0
  · subst hm0
    rcases hm with ⟨c, hc⟩
    omega
  by_cases hm1 : m = 1
  · exact Or.inl hm1
  by_cases hmp : m = p
  · exact Or.inr hmp
  exfalso
  have hmle : m ≤ p := Nat.le_of_dvd (by omega) hm
  have : p % m = 0 := Nat.dvd_iff_mod_eq_zero.mp hm
  exact noDivIn_spec p (p - 1) hnd m (by omega) (by omega) this

/-- The wheel: the primes below the modulus `727`, together with `727` itself.  These serve as
the pool of witnesses for the Goldbach decompositions. -/
def wheelPrimes727 : List Nat :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
   97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191,
   193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293,
   307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419,
   421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541,
   547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653,
   659, 661, 673, 677, 683, 691, 701, 709, 719, 727]

set_option maxRecDepth 100000 in
/-- Every entry of the wheel passes the Boolean primality test. -/
theorem wheelPrimes727_isPrimeB : wheelPrimes727.all isPrimeB = true := by decide

/-- Every entry of the wheel is prime. -/
theorem prime_of_mem_wheelPrimes727 {p : Nat} (hp : p ∈ wheelPrimes727) : IsPrime p :=
  isPrime_of_isPrimeB (List.all_eq_true.mp wheelPrimes727_isPrimeB p hp)

/-- Every entry of the wheel is at least `2`. -/
theorem two_le_of_mem_wheelPrimes727 {p : Nat} (hp : p ∈ wheelPrimes727) : 2 ≤ p :=
  (prime_of_mem_wheelPrimes727 hp).1

/-- The wheel search: for every even `n` with `4 ≤ n ≤ 727` some wheel prime `p` has `n - p`
again a wheel prime. -/
def wheelSearch727 : Bool :=
  (List.range 728).all fun n =>
    !(decide (4 ≤ n) && (n % 2 == 0)) ||
      wheelPrimes727.any fun p => wheelPrimes727.contains (n - p)

set_option maxRecDepth 100000 in
theorem wheelSearch727_eq_true : wheelSearch727 = true := by decide

theorem exists_wheel_split_727 {n : Nat} (hn : n < 728) (h4 : 4 ≤ n) (hev : n % 2 = 0) :
    ∃ p ∈ wheelPrimes727, (n - p) ∈ wheelPrimes727 := by
  have h := List.all_eq_true.mp wheelSearch727_eq_true n (List.mem_range.mpr hn)
  simp only [h4, hev, decide_true, Bool.true_and, Bool.not_true, Bool.false_or,
    beq_self_eq_true, List.any_eq_true, List.contains_iff_mem] at h
  obtain ⟨p, hp, hq⟩ := h
  exact ⟨p, hp, hq⟩

/-- **Goldbach wheel, `K = 2`, modulus `727`.**
Every even natural number `n` with `4 ≤ n ≤ 727` is a sum of two primes. -/
theorem GoldbachWheelK2_727 :
    ∀ n : Nat, 4 ≤ n → n ≤ 727 → n % 2 = 0 → GoldbachK2 n := by
  intro n h4 h727 hev
  obtain ⟨p, hp, hq⟩ := exists_wheel_split_727 (by omega) h4 hev
  have h2q : 2 ≤ n - p := two_le_of_mem_wheelPrimes727 hq
  exact ⟨p, n - p, prime_of_mem_wheelPrimes727 hp, prime_of_mem_wheelPrimes727 hq, by omega⟩

end Brockian

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

