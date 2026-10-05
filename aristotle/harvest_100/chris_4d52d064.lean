import Mathlib
import RequestProject.GoldbachWheelK2_727

/-!
# Goldbach Wheel K 2 727 — Mathlib bridge

The target theorem `Brockian.GoldbachWheelK2_727` lives in a Mathlib-free file (a module
docstring may not precede `import`, so the required header comment forces that file to be
import-free).  Here we identify the primality predicate used there with Mathlib's
`Nat.Prime` and restate the result accordingly.
-/

namespace Brockian

/-- The from-first-principles primality predicate agrees with Mathlib's `Nat.Prime`. -/
theorem isPrimeNat_iff_prime {n : ℕ} : IsPrimeNat n ↔ Nat.Prime n := by
  constructor
  · rintro ⟨h2, hd⟩
    exact Nat.prime_def.mpr ⟨h2, hd⟩
  · intro hp
    exact ⟨hp.two_le, fun d hd => hp.eq_one_or_self_of_dvd d hd⟩

/-- **Goldbach wheel, K = 2, bound 727**, stated with Mathlib's `Nat.Prime`:
every even number `2 * n` with `2 ≤ n ≤ 727` is a sum of two primes. -/
theorem GoldbachWheelK2_727_natPrime :
    ∀ n : ℕ, 2 ≤ n → n ≤ 727 → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ 2 * n = p + q := by
  intro n h2 h727
  obtain ⟨p, q, hp, hq, hpq⟩ := GoldbachWheelK2_727 n h2 h727
  exact ⟨p, q, isPrimeNat_iff_prime.mp hp, isPrimeNat_iff_prime.mp hq, hpq⟩

#print axioms GoldbachWheelK2_727
#print axioms GoldbachWheelK2_727_natPrime

end Brockian

/-!
# Goldbach Wheel K 2 727
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_727
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Brockian

/-- Primality of a natural number, stated from first principles.
(`Brockian.isPrimeNat_iff_prime` in `RequestProject.GoldbachWheelK2_727Mathlib`
identifies this with Mathlib's `Nat.Prime`.) -/
def IsPrimeNat (n : Nat) : Prop := 2 ≤ n ∧ ∀ d : Nat, d ∣ n → d = 1 ∨ d = n

/-- `noFactorFrom f d n` checks, using `f` units of fuel, that no `k ≥ d` with `k * k ≤ n`
divides `n`.  Exhausting the fuel returns `false`, so a `true` answer always comes from a
completed search; this makes the test sound by construction. -/
def noFactorFrom : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | (f + 1), d, n =>
      if n < d * d then true else if n % d == 0 then false else noFactorFrom f (d + 1) n

/-- A kernel-friendly primality test: trial division up to the square root. -/
def isPrimeFast (n : Nat) : Bool := Nat.ble 2 n && noFactorFrom n 2 n

/-- Soundness of the trial-division loop, by induction on the fuel. -/
theorem noFactorFrom_sound :
    ∀ (f d n k : Nat), noFactorFrom f d n = true → d ≤ k → k * k ≤ n → ¬ (k ∣ n) := by
  intro f
  induction f with
  | zero => intro d n k h _ _ _; exact Bool.noConfusion h
  | succ f ih =>
      intro d n k h hdk hkk hdvd
      rw [noFactorFrom] at h
      by_cases hlt : n < d * d
      · exact absurd (Nat.le_trans (Nat.mul_le_mul hdk hdk) hkk) (Nat.not_le.mpr hlt)
      · rw [if_neg hlt] at h
        by_cases hmod : n % d == 0
        · rw [if_pos hmod] at h; exact Bool.noConfusion h
        · rw [if_neg hmod] at h
          rcases Nat.eq_or_lt_of_le hdk with rfl | hlt'
          · obtain ⟨c, rfl⟩ := hdvd
            exact hmod (by simp [Nat.mul_mod_right])
          · exact ih (d + 1) n k h hlt' hkk hdvd

/-- The fast primality test is sound. -/
theorem isPrimeFast_sound {n : Nat} (h : isPrimeFast n = true) : IsPrimeNat n := by
  rw [isPrimeFast, Bool.and_eq_true] at h
  obtain ⟨h2, hnf⟩ := h
  have h2' : 2 ≤ n := Nat.le_of_ble_eq_true h2
  refine ⟨h2', fun d hd => ?_⟩
  obtain ⟨e, he⟩ := hd
  rcases Nat.lt_or_ge d 2 with hd2 | hd2
  · -- `d = 0` is impossible since `n ≥ 2`; so `d = 1`.
    rcases (by omega : d = 0 ∨ d = 1) with rfl | rfl
    · rw [Nat.zero_mul] at he; omega
    · exact Or.inl rfl
  · -- `d ≥ 2`: the trial division rules out `d * d ≤ n`, so `e < d`.
    have hdd : ¬ (d * d ≤ n) := fun hle =>
      noFactorFrom_sound n 2 n d hnf hd2 hle ⟨e, he⟩
    have hdpos : 0 < d := by omega
    have hed : e < d := by
      rcases Nat.lt_or_ge e d with hlt | hge
      · exact hlt
      · exact absurd (Nat.le_trans (Nat.mul_le_mul (Nat.le_refl d) hge)
          (Nat.le_of_eq he.symm)) hdd
    have he1 : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with rfl | hpos
      · rw [Nat.mul_zero] at he; omega
      · exact hpos
    rcases Nat.lt_or_ge e 2 with he2 | he2
    · have hE : e = 1 := by omega
      subst hE
      right; omega
    · exact absurd (show e ∣ n from ⟨d, by rw [he]; exact Nat.mul_comm d e⟩)
        (noFactorFrom_sound n 2 n e hnf he2
          (Nat.le_trans (Nat.mul_le_mul (Nat.le_refl e) (Nat.le_of_lt hed))
            (Nat.le_of_eq (by rw [he]; exact Nat.mul_comm e d))))

/-- Search for the least `p ≥ p₀` such that both `p` and `m - p` pass the primality test. -/
def findPrimePair : Nat → Nat → Nat → Nat
  | 0, p, _ => p
  | (f + 1), p, m => if isPrimeFast p && isPrimeFast (m - p) then p else findPrimePair f (p + 1) m

/-- The small prime in the Goldbach decomposition of `m` found by the search. -/
def gbP (m : Nat) : Nat := findPrimePair m 2 m

/-- Boolean certificate that `m` is a sum of two primes, namely `gbP m + (m - gbP m)`. -/
def gbGood (m : Nat) : Bool :=
  isPrimeFast (gbP m) && isPrimeFast (m - gbP m) && Nat.ble (gbP m) m

/-- The certificate holds for every even number `2 * n` with `2 ≤ n ≤ 727`. -/
theorem gbGood_all : (List.range 726).all (fun i => gbGood (2 * (i + 2))) = true := by
  decide

/-- **Goldbach wheel, K = 2, bound 727.**  Every even number `2 * n` with `2 ≤ n ≤ 727`
(i.e. every even number from `4` up to `1454`) is a sum of two primes. -/
theorem GoldbachWheelK2_727 :
    ∀ n : Nat, 2 ≤ n → n ≤ 727 → ∃ p q : Nat, IsPrimeNat p ∧ IsPrimeNat q ∧ 2 * n = p + q := by
  intro n h2 h727
  have hmem : (n - 2) ∈ List.range 726 := by
    rw [List.mem_range]; omega
  have hg : gbGood (2 * ((n - 2) + 2)) = true := List.all_eq_true.mp gbGood_all _ hmem
  rw [show (n - 2) + 2 = n by omega] at hg
  rw [gbGood, Bool.and_eq_true, Bool.and_eq_true] at hg
  obtain ⟨⟨hp, hq⟩, hle⟩ := hg
  refine ⟨gbP (2 * n), 2 * n - gbP (2 * n), isPrimeFast_sound hp, isPrimeFast_sound hq, ?_⟩
  have hle' : gbP (2 * n) ≤ 2 * n := Nat.le_of_ble_eq_true hle
  omega

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

