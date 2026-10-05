import Mathlib
import RequestProject.GoldbachWheelK2_947

/-!
# Goldbach Wheel K 2 947 — Mathlib interface

The target theorem `Brockian.GoldbachWheelK2_947` lives in the self-contained file
`RequestProject/GoldbachWheelK2_947.lean` (which carries no imports, since its header
comment must be the first thing in the file). Here we identify the primality notion used
there with Mathlib's `Nat.Prime` and restate the result in Mathlib terms.
-/

namespace Brockian

/-- The self-contained primality predicate agrees with Mathlib's `Nat.Prime`. -/
theorem isPrimeNat_iff_prime {p : ℕ} : IsPrimeNat p ↔ Nat.Prime p :=
  Nat.prime_def.symm

/-- **Goldbach wheel with modulus `947`, Mathlib form.**
Every even `n` with `4 ≤ n ≤ 1894` is a sum of two primes. -/
theorem goldbachWheelK2_947_mathlib (n : ℕ) (h4 : 4 ≤ n) (hle : n ≤ 2 * 947) (hev : Even n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n := by
  obtain ⟨p, q, hp, hq, hpq⟩ := GoldbachWheelK2_947 n h4 hle (Nat.even_iff.mp hev)
  exact ⟨p, q, isPrimeNat_iff_prime.mp hp, isPrimeNat_iff_prime.mp hq, hpq⟩

end Brockian

/-!
# Goldbach Wheel K 2 947
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_947
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 40000

namespace Brockian

/-! ## Primality

This file is self-contained (it has no `import`s, since the header comment above must be the
first thing in the file), so primality is developed from scratch, in the standard way:
`IsPrimeNat p` says that `p ≥ 2` and the only divisors of `p` are `1` and `p`.
A companion file identifies this notion with Mathlib's `Nat.Prime`. -/

/-- `p` is prime: `p ≥ 2` and every divisor of `p` is `1` or `p`. -/
def IsPrimeNat (p : Nat) : Prop := 2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

/-- `noDivBelow n k = true` iff no `d` with `2 ≤ d ≤ k` divides `n`. -/
def noDivBelow (n : Nat) : Nat → Bool
  | 0 => true
  | 1 => true
  | (k + 2) => (n % (k + 2) != 0) && noDivBelow n (k + 1)

theorem noDivBelow_sound {n : Nat} : ∀ {k : Nat}, noDivBelow n k = true →
    ∀ d : Nat, 2 ≤ d → d ≤ k → n % d ≠ 0 := by
  intro k
  induction k with
  | zero => intro _ d hd1 hd2; omega
  | succ k ih =>
    match k with
    | 0 => intro _ d hd1 hd2; omega
    | (k + 1) =>
      intro h d hd1 hd2
      simp only [noDivBelow, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      rcases Nat.lt_or_ge d (k + 2) with hlt | hge
      · exact ih h.2 d hd1 (by omega)
      · have hdk : d = k + 2 := by omega
        subst hdk; exact h.1

/-- Trial division is sound: if `n ≥ 2` has no divisor in `[2, k]` and `n < (k+1)^2`,
then `n` is prime. -/
theorem isPrimeNat_of_noDivBelow {n k : Nat} (h2 : 2 ≤ n) (hk : n < (k + 1) * (k + 1))
    (h : noDivBelow n k = true) : IsPrimeNat n := by
  refine ⟨h2, ?_⟩
  intro d hd
  rcases Classical.em (d = 1) with h1 | hd1
  · exact Or.inl h1
  rcases Classical.em (d = n) with h1 | hdn
  · exact Or.inr h1
  exfalso
  obtain ⟨e, he⟩ := hd
  subst he
  have hd0 : d ≠ 0 := by rintro rfl; rw [Nat.zero_mul] at h2; omega
  have he0 : e ≠ 0 := by rintro rfl; rw [Nat.mul_zero] at h2; omega
  have he1 : e ≠ 1 := by rintro rfl; rw [Nat.mul_one] at hdn; exact hdn rfl
  have hd2 : 2 ≤ d := by omega
  have he2 : 2 ≤ e := by omega
  have key : ∀ a b : Nat, 2 ≤ a → a ≤ b → a * b < (k + 1) * (k + 1) →
      noDivBelow (a * b) k = true → False := by
    intro a b ha hab hlt hnd
    have hsq : a * a ≤ a * b := Nat.mul_le_mul_left a hab
    have hak : a ≤ k := by
      rcases Nat.lt_or_ge k a with hh | hh
      · have : (k + 1) * (k + 1) ≤ a * a := Nat.mul_le_mul (by omega) (by omega)
        omega
      · exact hh
    exact noDivBelow_sound hnd a ha hak (Nat.dvd_iff_mod_eq_zero.mp ⟨b, rfl⟩)
  rcases Nat.le_total d e with hle | hle
  · exact key d e hd2 hle hk h
  · exact key e d he2 hle (by rw [Nat.mul_comm]; exact hk) (by rw [Nat.mul_comm]; exact h)

/-- How far to trial divide: up to `44` (enough for `n < 45^2 = 2025`), but never beyond
`n - 1`, so that the test is also correct for small `n`. -/
def trialBound (n : Nat) : Nat := if n ≤ 45 then n - 1 else 44

/-- A primality test, correct for `n ≤ 2024`. -/
def isPrimeB (n : Nat) : Bool := decide (2 ≤ n) && noDivBelow n (trialBound n)

theorem isPrimeB_sound {n : Nat} (hn : n ≤ 2024) (h : isPrimeB n = true) : IsPrimeNat n := by
  simp only [isPrimeB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h2, hnd⟩ := h
  refine isPrimeNat_of_noDivBelow h2 ?_ hnd
  unfold trialBound
  rcases Nat.lt_or_ge 45 n with hlt | hle
  · rw [if_neg (by omega)]
    omega
  · rw [if_pos hle]
    have hn1 : n - 1 + 1 = n := by omega
    rw [hn1]
    have hsq : 2 * n ≤ n * n := Nat.mul_le_mul_right n h2
    omega

/-! ## The Goldbach property -/

/-- `GoldbachK2 n` : `n` is a sum of two (not necessarily distinct) primes. -/
def GoldbachK2 (n : Nat) : Prop := ∃ p q : Nat, IsPrimeNat p ∧ IsPrimeNat q ∧ p + q = n

/-- The small primes used as the first summand; every even `n ≤ 1894` admits one of them. -/
def primeCands : List Nat := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 61, 67, 73]

/-- `hasPair n L = true` iff some `p ∈ L` with `p + 2 ≤ n` has both `p` and `n - p` prime. -/
def hasPair (n : Nat) : List Nat → Bool
  | [] => false
  | p :: ps => (decide (p + 2 ≤ n) && isPrimeB p && isPrimeB (n - p)) || hasPair n ps

theorem hasPair_sound {n : Nat} (hn : n ≤ 2024) :
    ∀ L : List Nat, hasPair n L = true → GoldbachK2 n := by
  intro L
  induction L with
  | nil => intro h; simp [hasPair] at h
  | cons p ps ih =>
    intro h
    simp only [hasPair, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨hple, hp⟩, hq⟩ | h
    · exact ⟨p, n - p, isPrimeB_sound (by omega) hp, isPrimeB_sound (by omega) hq, by omega⟩
    · exact ih h

/-- `allPairsUpTo m = true` iff `hasPair (2 * j) primeCands` holds for all `2 ≤ j ≤ m`. -/
def allPairsUpTo : Nat → Bool
  | 0 => true
  | 1 => true
  | (k + 2) => hasPair (2 * (k + 2)) primeCands && allPairsUpTo (k + 1)

theorem allPairsUpTo_sound : ∀ {m : Nat}, allPairsUpTo m = true →
    ∀ j : Nat, 2 ≤ j → j ≤ m → hasPair (2 * j) primeCands = true := by
  intro m
  induction m with
  | zero => intro _ j hj1 hj2; omega
  | succ m ih =>
    match m with
    | 0 => intro _ j hj1 hj2; omega
    | (m + 1) =>
      intro h j hj1 hj2
      simp only [allPairsUpTo, Bool.and_eq_true] at h
      rcases Nat.lt_or_ge j (m + 2) with hlt | hge
      · exact ih h.2 j hj1 (by omega)
      · have hj : j = m + 2 := by omega
        subst hj; exact h.1

/-- The verified computation: every even number `2 * j` with `2 ≤ j ≤ 947` has a Goldbach
pair among `primeCands`. -/
theorem allPairsUpTo_947 : allPairsUpTo 947 = true := by decide

/-- **Goldbach wheel with modulus `947`.**
Every even number `n` with `4 ≤ n ≤ 2 * 947 = 1894` is a sum of two primes. -/
theorem GoldbachWheelK2_947 :
    ∀ n : Nat, 4 ≤ n → n ≤ 2 * 947 → n % 2 = 0 → GoldbachK2 n := by
  intro n h4 hle hpar
  have hn : n = 2 * (n / 2) := by omega
  rw [hn]
  exact hasPair_sound (by omega) primeCands
    (allPairsUpTo_sound allPairsUpTo_947 (n / 2) (by omega) (by omega))

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

