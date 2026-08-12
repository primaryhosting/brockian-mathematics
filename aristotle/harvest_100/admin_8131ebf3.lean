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
# Odd Weird Exists
Category: Brockian Conjecture
Target: Brockian.WeirdNumbers.OddWeirdExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Weird Exists
Category: Brockian Conjecture
Target: Brockian.WeirdNumbers.OddWeirdExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

A natural number `n` is *weird* (`Nat.Weird`) if it is abundant (the sum of its proper
divisors exceeds `n`) but not pseudoperfect (no subset of its proper divisors sums to `n`).

Whether an **odd** weird number exists is a well-known open problem; no odd weird number is
known.  Consequently the file below does not claim an unconditional existence proof.
Instead it provides a Lean-checked *reduction*:

* `Brockian.WeirdNumbers.weird_mul_prime` : if `n` is weird and `p` is a prime exceeding the
  sum of the divisors of `n`, then `n * p` is weird.
* `Brockian.WeirdNumbers.OddWeirdExists` : an odd weird number exists **iff** there are
  arbitrarily large odd weird numbers.  In other words, a single odd weird number would
  immediately yield infinitely many.

Unconditionally we also record:

* `Brockian.WeirdNumbers.even_weird_exists` : `70` is an (even) weird number;
* `Brockian.WeirdNumbers.odd_weird_ge_1000` : every odd weird number is at least `1000`
  (the only odd abundant number below `1000` is `945`, and `945` is pseudoperfect).
-/

namespace Brockian.WeirdNumbers

open Finset

/-- The sum of all divisors of `n`. -/
abbrev sigmaOne (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- For a prime `p` not dividing `n`, `σ (n * p) = σ n * (p + 1)`. -/
lemma sigmaOne_mul_prime {n p : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n) :
    sigmaOne (n * p) = sigmaOne n * (p + 1) := by
  have hcop : Nat.Coprime n p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hpn).symm
  show ∑ d ∈ (n * p).divisors, d = (∑ d ∈ n.divisors, d) * (p + 1)
  rw [Nat.Coprime.sum_divisors_mul hcop]
  congr 1
  rw [hp.divisors, Finset.sum_pair hp.one_lt.ne, Nat.add_comm]

/-- A weird number is positive. -/
lemma Weird.pos {n : ℕ} (h : n.Weird) : 0 < n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact absurd h.1 Nat.not_abundant_zero
  · exact hn

/-- Twice a weird number is smaller than the sum of its divisors. -/
lemma two_mul_lt_sigmaOne {n : ℕ} (h : n.Weird) : 2 * n < sigmaOne n := by
  have habund := h.1
  have hsum : sigmaOne n = (∑ i ∈ n.properDivisors, i) + n :=
    Nat.sum_divisors_eq_sum_properDivisors_add_self
  unfold Nat.Abundant at habund
  omega

/-- If `n` is weird and `p` is a prime larger than the sum of the divisors of `n`,
then `n * p` is abundant. -/
lemma abundant_mul_prime {n p : ℕ} (hn : n.Weird) (hp : p.Prime) (hlt : sigmaOne n < p) :
    (n * p).Abundant := by
  have hnpos : 0 < n := Weird.pos hn
  have hn_le : n ≤ sigmaOne n :=
    Finset.single_le_sum (f := fun d : ℕ => d) (fun i _ => Nat.zero_le i)
      (Nat.mem_divisors_self n hnpos.ne')
  have hpn : ¬ p ∣ n := fun hd => by
    have := Nat.le_of_dvd hnpos hd
    omega
  have hsig := sigmaOne_mul_prime (n := n) hp hpn
  have h2 : 2 * n < sigmaOne n := two_mul_lt_sigmaOne hn
  have hsum : sigmaOne (n * p) = (∑ i ∈ (n * p).properDivisors, i) + n * p :=
    Nat.sum_divisors_eq_sum_properDivisors_add_self
  have hp1 : 1 ≤ p := hp.pos
  show n * p < ∑ i ∈ (n * p).properDivisors, i
  nlinarith [hsig, hsum, h2, hp1]

/-- If `n` is weird and `p` is a prime larger than the sum of the divisors of `n`,
then `n * p` is not pseudoperfect. -/
lemma not_pseudoperfect_mul_prime {n p : ℕ} (hn : n.Weird) (hp : p.Prime)
    (hlt : sigmaOne n < p) : ¬ (n * p).Pseudoperfect := by
  rintro ⟨-, S, hS, hSsum⟩
  have hnpos : 0 < n := Weird.pos hn
  have hppos : 0 < p := hp.pos
  classical
  set A := S.filter (fun d => ¬ p ∣ d) with hA
  set B := S.filter (fun d => p ∣ d) with hB
  have hsplit : (∑ d ∈ B, d) + (∑ d ∈ A, d) = n * p := by
    rw [hA, hB, Finset.sum_filter_add_sum_filter_not S (fun d => p ∣ d)]
    exact hSsum
  -- the part of `S` coprime to `p` consists of divisors of `n`
  have hAsub : A ⊆ n.divisors := by
    intro d hd
    rw [hA, Finset.mem_filter] at hd
    obtain ⟨hdS, hdp⟩ := hd
    have hd' := hS hdS
    rw [Nat.mem_properDivisors] at hd'
    have hcop : Nat.Coprime d p := ((hp.coprime_iff_not_dvd).2 hdp).symm
    exact Nat.mem_divisors.2 ⟨hcop.dvd_of_dvd_mul_right hd'.1, by positivity⟩
  have hAle : (∑ d ∈ A, d) ≤ sigmaOne n :=
    Finset.sum_le_sum_of_subset hAsub
  have hdvdB : p ∣ ∑ d ∈ B, d :=
    Finset.dvd_sum (fun d hd => (Finset.mem_filter.1 (hB ▸ hd)).2)
  have hdvdA : p ∣ ∑ d ∈ A, d := by
    refine (Nat.dvd_add_right hdvdB).mp ?_
    rw [hsplit]
    exact dvd_mul_left p n
  have hA0 : (∑ d ∈ A, d) = 0 := by
    by_contra h0
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hdvdA
    omega
  have hBsum : (∑ d ∈ B, d) = n * p := by omega
  -- divide the `p`-divisible part by `p`
  have hBdvd : ∀ d ∈ B, p ∣ d := fun d hd => (Finset.mem_filter.1 (hB ▸ hd)).2
  have hinj : ∀ x ∈ B, ∀ y ∈ B, x / p = y / p → x = y := by
    intro x hx y hy hxy
    have hx' := Nat.mul_div_cancel' (hBdvd x hx)
    have hy' := Nat.mul_div_cancel' (hBdvd y hy)
    rw [← hx', ← hy', hxy]
  set B' := B.image (fun d => d / p) with hB'
  have hsum' : p * (∑ e ∈ B', e) = n * p := by
    rw [hB', Finset.mul_sum, Finset.sum_image hinj]
    rw [← hBsum]
    exact Finset.sum_congr rfl (fun d hd => Nat.mul_div_cancel' (hBdvd d hd))
  have hB'sum : (∑ e ∈ B', e) = n := by
    have : p * (∑ e ∈ B', e) = p * n := by rw [hsum', Nat.mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hppos this
  have hB'sub : B' ⊆ n.properDivisors := by
    intro e he
    rw [hB', Finset.mem_image] at he
    obtain ⟨d, hd, rfl⟩ := he
    have hdmem := hS (Finset.mem_of_mem_filter d (hB ▸ hd))
    rw [Nat.mem_properDivisors] at hdmem
    have hdeq : p * (d / p) = d := Nat.mul_div_cancel' (hBdvd d hd)
    have hdvd : p * (d / p) ∣ p * n := by
      rw [hdeq, Nat.mul_comm p n]
      exact hdmem.1
    have hlt' : p * (d / p) < p * n := by
      rw [hdeq, Nat.mul_comm p n]
      exact hdmem.2
    exact Nat.mem_properDivisors.2
      ⟨(mul_dvd_mul_iff_left hppos.ne').1 hdvd, lt_of_mul_lt_mul_left hlt' (Nat.zero_le p)⟩
  exact hn.2 ⟨hnpos, B', hB'sub, hB'sum⟩

/-- If `n` is weird and `p` is a prime larger than the sum of the divisors of `n`,
then `n * p` is weird. -/
theorem weird_mul_prime {n p : ℕ} (hn : n.Weird) (hp : p.Prime) (hlt : sigmaOne n < p) :
    (n * p).Weird :=
  ⟨abundant_mul_prime hn hp hlt, not_pseudoperfect_mul_prime hn hp hlt⟩

/-- `70` is an even weird number, so weird numbers do exist. -/
theorem even_weird_exists : ∃ n : ℕ, Even n ∧ n.Weird :=
  ⟨70, by decide, Nat.weird_seventy⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- The only odd abundant number below `1000` is `945`. -/
lemma odd_abundant_lt_1000 : ∀ n < 1000, Odd n → Nat.Abundant n → n = 945 := by
  decide +kernel

/-- `945 = 1 + 9 + 21 + 27 + 35 + 45 + 63 + 105 + 135 + 189 + 315` is a sum of proper
divisors of `945`, so `945` is pseudoperfect. -/
lemma pseudoperfect_945 : Nat.Pseudoperfect 945 :=
  ⟨by norm_num, {1, 9, 21, 27, 35, 45, 63, 105, 135, 189, 315},
    by decide +kernel, by decide +kernel⟩

/-- **Partial result:** every odd weird number is at least `1000`. -/
theorem odd_weird_ge_1000 {n : ℕ} (hodd : Odd n) (hw : n.Weird) : 1000 ≤ n := by
  by_contra hlt
  push_neg at hlt
  have h945 : n = 945 := odd_abundant_lt_1000 n hlt hodd hw.1
  exact hw.2 (h945 ▸ pseudoperfect_945)

/-- **Conditional reduction for the odd weird number problem.**
An odd weird number exists if and only if there are arbitrarily large odd weird numbers.
(Whether either side holds is an open problem.) -/
theorem OddWeirdExists :
    (∃ n : ℕ, Odd n ∧ n.Weird) ↔ ∀ N : ℕ, ∃ n : ℕ, N < n ∧ Odd n ∧ n.Weird := by
  constructor
  · rintro ⟨n, hodd, hw⟩ N
    obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (max (sigmaOne n + 1) (N + 1))
    have hlt : sigmaOne n < p :=
      lt_of_lt_of_le (Nat.lt_succ_self _) (le_trans (le_max_left _ _) hpge)
    have hNp : N < p := lt_of_lt_of_le (Nat.lt_succ_self _) (le_trans (le_max_right _ _) hpge)
    have hnpos : 0 < n := Weird.pos hw
    have hp2 : p ≠ 2 := by
      have h2 : 2 * n < sigmaOne n := two_mul_lt_sigmaOne hw
      omega
    refine ⟨n * p, ?_, ?_, weird_mul_prime hw hp hlt⟩
    · calc N < p := hNp
        _ = 1 * p := (one_mul p).symm
        _ ≤ n * p := Nat.mul_le_mul_right p hnpos
    · exact hodd.mul (hp.odd_of_ne_two hp2)
  · intro h
    obtain ⟨n, _, hodd, hw⟩ := h 0
    exact ⟨n, hodd, hw⟩

end Brockian.WeirdNumbers

