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

import RequestProject.AKS.Algorithm

/-!
# Correctness of the AKS primality test

The main result of this file is `AKS.aksTest_iff_prime`:
the decision procedure `AKS.aksTest` returns `true` exactly on the primes.
-/

namespace AKS

open Polynomial Finset


theorem aksTest_iff_prime (n : ℕ) : aksTest n = true ↔ n.Prime := by
  constructor
  · intro h
    rw [aksTest] at h
    split at h
    · simp at h
    · rename_i hn2
      push_neg at hn2
      split at h
      · simp at h
      · rename_i hpp
        simp only at h
        set r := findR n with hrdef
        have hr2 : 2 ≤ r := two_le_findR n hn2
        split at h
        · simp at h
        · rename_i hgcd
          have hgcdOK : gcdOK n r = true := by
            rcases Bool.eq_false_or_eq_true (gcdOK n r) with h1 | h1
            · exact absurd h1 hgcd
            · exact h1
          have hg := (gcdOK_iff n r).1 hgcdOK
          split at h
          · rename_i hle
            exact prime_of_gcdOK_le hn2 hle hg
          · rename_i hle
            push_neg at hle
            -- now `r < n`
            have hrn : r < n := hle
            have hcop1 := gcd_one_of_gcdOK hrn hg
            -- every prime factor of `n` exceeds `r`
            have hbig : ∀ q : ℕ, q.Prime → q ∣ n → r < q := by
              intro q hq hqn
              by_contra hqr
              push_neg at hqr
              have : Nat.gcd q n = q := Nat.gcd_eq_left hqn
              have := hcop1 q hq.two_le hqr
              omega
            have hcopn : Nat.Coprime n r := by
              rw [Nat.coprime_comm]
              rw [Nat.coprime_iff_gcd_eq_one]
              by_contra hgc
              obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hgc
              have hqr : q ∣ r := hqd.trans (Nat.gcd_dvd_left r n)
              have hqn : q ∣ n := hqd.trans (Nat.gcd_dvd_right r n)
              have := hbig q hq hqn
              have := Nat.le_of_dvd (by omega) hqr
              omega
            set p := n.minFac with hpdef
            have hp : p.Prime := Nat.minFac_prime (by omega)
            have hpn : p ∣ n := Nat.minFac_dvd n
            have hrp : r < p := hbig p hp hpn
            have hord : ∀ i, 1 ≤ i → i ≤ 100 * (bitLen n) ^ 2 → (n : ZMod r) ^ i ≠ 1 := by
              intro i hi1 hi2 hcon
              have := findR_ord n hn2 i hi1 (by simpa [thr] using hi2)
              apply this
              have h1 : ((n ^ i : ℕ) : ZMod r) = ((1 : ℕ) : ZMod r) := by
                push_cast
                simpa using hcon
              have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).1 h1
              have h3 : n ^ i % r = 1 % r := h2
              rwa [Nat.mod_eq_of_lt (by omega)] at h3
            have hintro : ∀ a : ℕ, a ≤ 4 * (Nat.sqrt r + 1) * bitLen n →
                Introspective r n ((X + C ((a : ℕ) : ZMod n)) : (ZMod n)[X]) := by
              intro a ha
              have hmem : a ∈ List.range (ell n r + 1) := by
                rw [List.mem_range]
                simpa [ell] using Nat.lt_succ_of_le ha
              have := List.all_eq_true.1 h a hmem
              exact introspective_of_polyOK (by omega) this
            obtain ⟨k, hk⟩ := prime_pow_of_introspective n r p (bitLen n) hp hn2
              (lt_two_pow_bitLen n) hr2 hcopn hpn hrp hord hintro
            rcases Nat.lt_or_ge k 2 with hk2 | hk2
            · interval_cases k
              · simp at hk; omega
              · rw [pow_one] at hk; rwa [hk]
            · exfalso
              have : isPerfectPower n = true := (isPerfectPower_iff n hn2).2 ⟨p, k, hk2, hk⟩
              rw [this] at hpp
              simp at hpp
  · intro hp
    haveI : Fact n.Prime := ⟨hp⟩
    have hn2 : 2 ≤ n := hp.two_le
    rw [aksTest]
    rw [if_neg (by omega)]
    have hpp : isPerfectPower n = false := by
      rcases Bool.eq_false_or_eq_true (isPerfectPower n) with h1 | h1
      · exact h1
      · exfalso
        obtain ⟨a, b, hb, hab⟩ := (isPerfectPower_iff n hn2).1 h1
        have hadvd : a ∣ n := ⟨a ^ (b - 1), by rw [hab, ← pow_succ']; congr 1; omega⟩
        rcases (Nat.Prime.eq_one_or_self_of_dvd hp a hadvd) with h2 | h2
        · rw [h2, one_pow] at hab; omega
        · subst h2
          have : a ^ 2 ≤ a ^ b := Nat.pow_le_pow_right (by omega) hb
          rw [← hab] at this
          nlinarith
    rw [hpp]
    simp only [Bool.false_eq_true, if_false]
    have hr2 : 2 ≤ findR n := two_le_findR n hn2
    have hgcdOK : gcdOK n (findR n) = true := by
      rw [gcdOK_iff]
      intro a _ _
      rcases hp.eq_one_or_self_of_dvd (Nat.gcd a n) (Nat.gcd_dvd_right a n) with h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1
    simp only [hgcdOK, Bool.true_eq_false, if_false]
    split
    · rfl
    · refine List.all_eq_true.2 fun a _ => polyOK_of_prime (by omega) a

end AKS

import RequestProject.AKS.Introspective
import RequestProject.AKS.Numeric

/-!
# The AKS criterion

The main theorem of this file, `AKS.prime_pow_of_introspective`, is the mathematical heart of
the Agrawal–Kayal–Saxena primality test: if `n` passes the polynomial congruence tests
`(X + a)^n ≡ X^n + a  (mod X^r - 1, n)` for enough values of `a`, and the multiplicative order
of `n` modulo `r` is large, then `n` is a power of a prime.
-/

namespace AKS

open Polynomial Finset

/-! ## Numeric preliminaries -/

