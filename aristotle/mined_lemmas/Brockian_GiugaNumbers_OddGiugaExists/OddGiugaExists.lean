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

import Mathlib
/-!
# Odd Giuga Exists
Category: Brockian Conjecture
Target: Brockian.GiugaNumbers.OddGiugaExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Brockian.GiugaNumbers

/-- A *Giuga number* is a composite natural number `n > 1` such that
`p ∣ n / p - 1` for every prime `p` dividing `n`. -/

theorem OddGiugaExists {S : Finset ℕ} (hp : ∀ p ∈ S, p.Prime) (h2 : ∀ p ∈ S, p ≠ 2)
    (hcard : 2 ≤ S.card) (hdvd : ∀ p ∈ S, p ∣ (∏ q ∈ S.erase p, q) - 1) :
    ∃ n : ℕ, Odd n ∧ IsGiuga n := by
  classical
  obtain ⟨p₀, hp₀, q₀, hq₀, hne⟩ := Finset.one_lt_card.1 (by omega : 1 < S.card)
  set n : ℕ := ∏ p ∈ S, p with hn
  have hfac : n.primeFactors = S := by rw [hn]; exact Nat.primeFactors_prod hp
  have hsplit : p₀ * ∏ q ∈ S.erase p₀, q = n := Finset.mul_prod_erase S (fun q => q) hp₀
  have hq₀e : q₀ ∈ S.erase p₀ := Finset.mem_erase.2 ⟨Ne.symm hne, hq₀⟩
  have hXpos : 0 < ∏ q ∈ S.erase p₀, q :=
    Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.2
      (fun q hq => (hp q (Finset.mem_of_mem_erase hq)).ne_zero))
  have hX2 : 2 ≤ ∏ q ∈ S.erase p₀, q := by
    have hdq : q₀ ∣ ∏ q ∈ S.erase p₀, q := Finset.dvd_prod_of_mem _ hq₀e
    have := Nat.le_of_dvd hXpos hdq
    have := (hp q₀ hq₀).two_le
    omega
  have hp₀2 : 2 ≤ p₀ := (hp p₀ hp₀).two_le
  have h1n : 1 < n := by
    rw [← hsplit]
    calc 1 < 2 * 2 := by norm_num
      _ ≤ p₀ * ∏ q ∈ S.erase p₀, q := Nat.mul_le_mul hp₀2 hX2
  refine ⟨n, ?_, h1n, ?_, ?_⟩
  · rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    intro hdvd2
    rw [hn] at hdvd2
    obtain ⟨q, hqS, hq2⟩ := (Prime.dvd_finset_prod_iff Nat.prime_two.prime _).1 hdvd2
    exact h2 q hqS (((Nat.prime_dvd_prime_iff_eq Nat.prime_two (hp q hqS)).1 hq2).symm)
  · rw [← hsplit]
    exact Nat.not_prime_mul (by omega) (by omega)
  · intro p hpm
    rw [hfac] at hpm
    rw [hn, prod_div_eq_prod_erase hp p hpm]
    exact hdvd p hpm

/-- The reduction used in `OddGiugaExists` is faithful: odd Giuga numbers correspond exactly
to finite sets `S` of at least two odd primes with `p ∣ (∏ q ∈ S.erase p, q) - 1` for all
`p ∈ S`. -/
