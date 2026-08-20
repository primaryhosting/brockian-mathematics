/-!
# Goldbach Wheel K 2 1327
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1327
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately import-free: Lean 4 does not allow a module docstring
(`/-! ... -/`) to precede the `import` commands, so the required header comment
forces the development to be self-contained in core Lean.  The primality
predicate is therefore spelled out explicitly (`2 ≤ p ∧ every divisor of p is 1
or p`).  The companion file `RequestProject.GoldbachWheelK2_1327Mathlib`
imports Mathlib and restates the result with `Nat.Prime`.
-/

namespace Brockian

/-- `noFacB n k = true` certifies that no `m` with `2 ≤ m ≤ k` and `m * m ≤ n` divides `n`.
Trial divisions are skipped as soon as `m * m > n`, which keeps kernel evaluation cheap. -/
def noFacB (n : Nat) : Nat → Bool
  | 0 => true
  | (k + 1) =>
      (if k + 1 < 2 ∨ n < (k + 1) * (k + 1) then true else !(n % (k + 1) == 0)) && noFacB n k

/-- A primality certificate for naturals `n ≤ 1680`: trial division by all `m ≤ 40`. -/
def primeCert (n : Nat) : Bool := (2 ≤ n) && noFacB n 40

/-- A Goldbach certificate for `n`: some `p < n` passes `primeCert` and so does `n - p`. -/
def gbCert (n : Nat) : Bool := (List.range n).any fun p => primeCert p && primeCert (n - p)

/-- The explicit primality predicate used in the statement below. -/
def IsPrimeNat (p : Nat) : Prop := 2 ≤ p ∧ ∀ m, m ∣ p → m = 1 ∨ m = p

theorem noFacB_sound :
    ∀ (k n m : Nat), noFacB n k = true → 2 ≤ m → m ≤ k → m * m ≤ n → ¬ m ∣ n := by
  intro k
  induction k with
  | zero => intro n m _ hm hmk _; omega
  | succ k ih =>
      intro n m h hm hmk hmn
      rw [noFacB, Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      rcases Nat.lt_or_ge m (k + 1) with hlt | hge
      · exact ih n m h2 hm (by omega) hmn
      · have hmeq : m = k + 1 := by omega
        subst hmeq
        rw [if_neg (by omega)] at h1
        rw [Nat.dvd_iff_mod_eq_zero]
        simpa using h1

/-- If no `m` with `2 ≤ m` and `m * m ≤ n` divides `n`, then `n` is prime. -/
theorem isPrimeNat_of_no_small_factor {n : Nat} (h2 : 2 ≤ n)
    (h : ∀ m, 2 ≤ m → m * m ≤ n → ¬ m ∣ n) : IsPrimeNat n := by
  refine ⟨h2, fun m hmd => ?_⟩
  rcases Decidable.em (m = 1) with hm1 | hm1
  · exact Or.inl hm1
  rcases Decidable.em (m = n) with hmn | hmn
  · exact Or.inr hmn
  exfalso
  have hm0 : m ≠ 0 := by
    intro h0
    subst h0
    exact absurd (Nat.eq_zero_of_zero_dvd hmd) (by omega)
  have hmle : m ≤ n := Nat.le_of_dvd (by omega) hmd
  have hm2 : 2 ≤ m := by omega
  have hmlt : m < n := by omega
  obtain ⟨c, hnc⟩ := id hmd
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, Nat.mul_zero] at hnc
    omega
  have hc1 : c ≠ 1 := by
    intro h1
    rw [h1, Nat.mul_one] at hnc
    omega
  have hc2 : 2 ≤ c := by omega
  have hcd : c ∣ n := ⟨m, by rw [hnc, Nat.mul_comm]⟩
  rcases Nat.lt_or_ge c m with hlt | hge
  · exact h c hc2 (by calc c * c ≤ m * c := Nat.mul_le_mul (Nat.le_of_lt hlt) (Nat.le_refl c)
                    _ = n := hnc.symm) hcd
  · exact h m hm2 (by calc m * m ≤ m * c := Nat.mul_le_mul (Nat.le_refl m) hge
                    _ = n := hnc.symm) hmd

theorem primeCert_sound {n : Nat} (hn : n ≤ 1680) (h : primeCert n = true) : IsPrimeNat n := by
  rw [primeCert, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h2, hnf⟩ := h
  refine isPrimeNat_of_no_small_factor h2 (fun m hm hmm => ?_)
  have hm40 : m ≤ 40 := by
    rcases Nat.lt_or_ge m 41 with h' | h'
    · omega
    · have : 41 * 41 ≤ m * m := Nat.mul_le_mul h' h'
      omega
  exact noFacB_sound 40 n m hnf hm hm40 hmm

theorem gbCert_sound {n : Nat} (hn : n ≤ 1680) (h : gbCert n = true) :
    ∃ p q : Nat, IsPrimeNat p ∧ IsPrimeNat q ∧ p + q = n := by
  rw [gbCert, List.any_eq_true] at h
  obtain ⟨p, hp, hpc⟩ := h
  rw [List.mem_range] at hp
  rw [Bool.and_eq_true] at hpc
  exact ⟨p, n - p, primeCert_sound (by omega) hpc.1,
    primeCert_sound (by omega) hpc.2, by omega⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
/-- The kernel-checked verification of the Goldbach property for every even
number `2 * k` with `2 ≤ k < 664`, i.e. for every even `n` with `4 ≤ n ≤ 1326`. -/
theorem gbCert_all : (List.range 664).all (fun k => k < 2 || gbCert (2 * k)) = true := by
  decide

/-- **Goldbach's conjecture on the `K = 2` wheel, verified up to `1327`.**
Every even natural number `n` with `4 ≤ n ≤ 1327` is a sum of two primes,
where primality is spelled out as `2 ≤ p ∧ ∀ m, m ∣ p → m = 1 ∨ m = p`. -/
theorem GoldbachWheelK2_1327 (n : Nat) (h4 : 4 ≤ n) (hn : n ≤ 1327) (he : n % 2 = 0) :
    ∃ p q : Nat, IsPrimeNat p ∧ IsPrimeNat q ∧ p + q = n := by
  have hk664 : n / 2 < 664 := by omega
  have hall := List.all_eq_true.mp gbCert_all (n / 2) (List.mem_range.mpr hk664)
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hall
  rcases hall with h | h
  · omega
  · have hn2 : 2 * (n / 2) = n := by omega
    rw [hn2] at h
    exact gbCert_sound (by omega) h

end Brockian

import Mathlib
import RequestProject.GoldbachWheelK2_1327

/-!
# Goldbach Wheel K 2 1327 — Mathlib restatement

`RequestProject.GoldbachWheelK2_1327` must begin with a module docstring, which Lean does not
allow to precede `import` commands; that file is therefore import-free and uses an explicit
primality predicate.  Here we import Mathlib and restate the same theorem with `Nat.Prime`.
-/

namespace Brockian

theorem isPrimeNat_iff_prime {p : ℕ} : IsPrimeNat p ↔ Nat.Prime p := by
  rw [Nat.prime_def]
  rfl

/-- **Goldbach's conjecture on the `K = 2` wheel, verified up to `1327`** (Mathlib form).
Every even `n` with `4 ≤ n ≤ 1327` is a sum of two primes. -/
theorem GoldbachWheelK2_1327_natPrime (n : ℕ) (h4 : 4 ≤ n) (hn : n ≤ 1327) (he : Even n) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  obtain ⟨p, q, hp, hq, hpq⟩ :=
    GoldbachWheelK2_1327 n h4 hn (Nat.even_iff.mp he)
  exact ⟨p, q, isPrimeNat_iff_prime.mp hp, isPrimeNat_iff_prime.mp hq, hpq⟩

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

