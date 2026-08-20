import Mathlib
import RequestProject.GoldbachWheelK2_947

/-!
Companion file: certifies that the self-contained primality predicate
`Brockian.IsPrime` used in `RequestProject/GoldbachWheelK2_947.lean` coincides with
Mathlib's `Nat.Prime`, and restates the main theorem in Mathlib terms.
-/

namespace Brockian

theorem isPrime_iff_nat_prime (n : Nat) : IsPrime n ↔ Nat.Prime n := by
  constructor
  · rintro ⟨h2, h⟩
    refine Nat.prime_def_lt.mpr ⟨h2, ?_⟩
    intro m hmn hdvd
    exact h m hmn hdvd
  · intro hp
    exact ⟨hp.two_le, fun m hmn hdvd => (Nat.prime_def_lt.mp hp).2 m hmn hdvd⟩

/-- Mathlib restatement of `Brockian.GoldbachWheelK2_947`: every even `n` with
`4 ≤ n ≤ 2 * 947` is a sum of two primes. -/
theorem goldbachWheelK2_947_mathlib (n : ℕ) (hev : Even n) (h4 : 4 ≤ n) (hle : n ≤ 2 * 947) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  obtain ⟨p, q, hp, hq, hpq⟩ := GoldbachWheelK2_947 n hev.two_dvd h4 hle
  exact ⟨p, q, (isPrime_iff_nat_prime p).mp hp, (isPrime_iff_nat_prime q).mp hq, hpq⟩

end Brockian

/-!
# Goldbach Wheel K 2 947
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_947
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately import-free (core Lean only), because Lean requires
`import` commands to precede every other command in a file, and the prescribed
header comment must come first.  Primality is therefore defined here from
scratch; the companion file `RequestProject/GoldbachWheelK2_947Mathlib.lean`
checks that `Brockian.IsPrime` agrees with Mathlib's `Nat.Prime`, and restates
the main theorem in Mathlib terms.
-/

namespace Brockian

/-- `IsPrime n` : `n` is at least `2` and its only proper divisor is `1`. -/
def IsPrime (n : Nat) : Prop := 2 ≤ n ∧ ∀ m, m < n → m ∣ n → m = 1

/-- Trial division: `trialDiv n fuel d` tests that no `e` with `d ≤ e` and `e * e ≤ n`
divides `n`, using at most `fuel` steps. -/
def trialDiv (n : Nat) : Nat → Nat → Bool
  | 0, _ => true
  | fuel + 1, d =>
      if n < d * d then true
      else if n % d == 0 then false
      else trialDiv n fuel (d + 1)

/-- A fast Boolean primality test by trial division up to the square root. -/
def isPrimeB (n : Nat) : Bool := 2 ≤ n && trialDiv n n 2

theorem trialDiv_sound : ∀ (fuel n d e : Nat), trialDiv n fuel d = true → d ≤ e →
    e * e ≤ n → e < d + fuel → ¬ e ∣ n := by
  intro fuel
  induction fuel with
  | zero => intro n d e _ h1 _ h3; omega
  | succ f ih =>
    intro n d e ht hde hen hlt
    rw [trialDiv] at ht
    by_cases hd : n < d * d
    · have : d * d ≤ e * e := Nat.mul_le_mul hde hde
      omega
    · simp only [hd, if_false] at ht
      by_cases hm : n % d == 0
      · simp [hm] at ht
      · simp only [hm] at ht
        rcases Nat.eq_or_lt_of_le hde with rfl | hlt2
        · intro hdvd
          have := Nat.dvd_iff_mod_eq_zero.mp hdvd
          simp at hm
          omega
        · exact ih n (d + 1) e ht hlt2 hen (by omega)

/-- Soundness of the Boolean primality test. -/
theorem isPrimeB_sound (n : Nat) (h : isPrimeB n = true) : IsPrime n := by
  unfold isPrimeB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h2, ht⟩ := h
  refine ⟨h2, ?_⟩
  intro m hmn hdvd
  by_cases hm1 : m = 1
  · exact hm1
  · exfalso
    have hm0 : m ≠ 0 := by rintro rfl; have := Nat.eq_zero_of_zero_dvd hdvd; omega
    have hm2 : 2 ≤ m := by omega
    obtain ⟨k, hk⟩ := hdvd
    have hk2 : 2 ≤ k := by
      rcases Nat.lt_or_ge k 2 with hlt | hge
      · match k, hlt with
        | 0, _ => simp at hk; omega
        | 1, _ => simp at hk; omega
      · exact hge
    rcases Nat.le_total m k with hmk | hmk
    · exact trialDiv_sound n n 2 m ht hm2
        (by calc m * m ≤ m * k := Nat.mul_le_mul_left m hmk
              _ = n := hk.symm) (by omega) ⟨k, hk⟩
    · exact trialDiv_sound n n 2 k ht hk2
        (by calc k * k ≤ m * k := Nat.mul_le_mul_right k hmk
              _ = n := hk.symm) (by omega) ⟨m, by rw [hk, Nat.mul_comm]⟩

/-- The `K = 2` Goldbach wheel: the list of prime spokes used to split every even
number `n` with `4 ≤ n ≤ 2 * 947` as `p + (n - p)` with both parts prime. -/
def goldbachWheelK2 : List Nat :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 61, 67, 73]

set_option maxRecDepth 20000 in
/-- **Key intermediate lemma.** The wheel `goldbachWheelK2` covers every even number
`n` with `4 ≤ n < 1895`: some spoke `p ≤ n` of the wheel has both `p` and `n - p`
prime (checked with the Boolean test `isPrimeB`). -/
theorem goldbachWheelK2_covers : ∀ n, n < 1895 → 2 ∣ n → 4 ≤ n →
    ∃ p ∈ goldbachWheelK2, p ≤ n ∧ isPrimeB p = true ∧ isPrimeB (n - p) = true := by
  decide

/-- **Goldbach wheel, K = 2, modulus 947.** Every even number `n` with
`4 ≤ n ≤ 2 * 947` is the sum of two primes. -/
theorem GoldbachWheelK2_947 : ∀ n : Nat, 2 ∣ n → 4 ≤ n → n ≤ 2 * 947 →
    ∃ p q : Nat, IsPrime p ∧ IsPrime q ∧ p + q = n := by
  intro n hev h4 hle
  obtain ⟨p, -, hpn, hp, hq⟩ := goldbachWheelK2_covers n (by omega) hev h4
  exact ⟨p, n - p, isPrimeB_sound p hp, isPrimeB_sound (n - p) hq, by omega⟩

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

