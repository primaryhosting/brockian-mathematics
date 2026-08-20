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
# Brocard Gap Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardGap.BrocardGapConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.BrocardGap

open Finset

/-- **Oppermann's conjecture**: for every `m > 1` there is a prime strictly between
`m² - m` and `m²`, and a prime strictly between `m²` and `m² + m`. -/
def OppermannConjecture : Prop :=
  ∀ m : ℕ, 1 < m →
    (∃ p : ℕ, p.Prime ∧ m * m - m < p ∧ p < m * m) ∧
    (∃ p : ℕ, p.Prime ∧ m * m < p ∧ p < m * m + m)

/-- The number of primes strictly between `a` and `b`. -/
def primesBetween (a b : ℕ) : ℕ := ((Finset.Ioo a b).filter Nat.Prime).card

/-- Four distinct primes in `Ioo a b` force `4 ≤ primesBetween a b`. -/
lemma four_le_primesBetween {a b p₁ p₂ p₃ p₄ : ℕ}
    (h₁ : p₁.Prime) (h₂ : p₂.Prime) (h₃ : p₃.Prime) (h₄ : p₄.Prime)
    (ha : a < p₁) (o₁ : p₁ < p₂) (o₂ : p₂ < p₃) (o₃ : p₃ < p₄) (hb : p₄ < b) :
    4 ≤ primesBetween a b := by
  have hsub : ({p₁, p₂, p₃, p₄} : Finset ℕ) ⊆ (Finset.Ioo a b).filter Nat.Prime := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_Ioo]
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨⟨ha, by omega⟩, h₁⟩
    · exact ⟨⟨by omega, by omega⟩, h₂⟩
    · exact ⟨⟨by omega, by omega⟩, h₃⟩
    · exact ⟨⟨by omega, hb⟩, h₄⟩
  have hcard : ({p₁, p₂, p₃, p₄} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp; omega),
      Finset.card_insert_of_notMem (by simp; omega),
      Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
  calc (4 : ℕ) = ({p₁, p₂, p₃, p₄} : Finset ℕ).card := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

/-- Consecutive odd primes differ by at least `2`. -/
lemma add_two_le_of_prime_lt {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hp3 : 3 ≤ p)
    (hpq : p < q) : p + 2 ≤ q := by
  rcases Nat.lt_or_ge q (p + 2) with h | h
  · exfalso
    have hqe : q = p + 1 := by omega
    have hpodd : ¬ (2 ∣ p) := fun hdvd => by
      have := (Nat.Prime.eq_one_or_self_of_dvd hp 2 hdvd); omega
    have hqodd : ¬ (2 ∣ q) := fun hdvd => by
      have := (Nat.Prime.eq_one_or_self_of_dvd hq 2 hdvd)
      omega
    have hcases : 2 ∣ p ∨ 2 ∣ (p + 1) := by omega
    rcases hcases with h' | h'
    · exact hpodd h'
    · exact hqodd (hqe ▸ h')
  · exact h

/-- Key step: assuming Oppermann's conjecture, for odd primes `p < q` there are at least four
primes strictly between `p²` and `q²`. -/
lemma four_le_primesBetween_sq (hOpp : OppermannConjecture) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hp3 : 3 ≤ p) (hpq : p < q) :
    4 ≤ primesBetween (p * p) (q * q) := by
  have hq2 : p + 2 ≤ q := add_two_le_of_prime_lt hp hq hp3 hpq
  -- a prime in `(p², p² + p)`
  obtain ⟨-, ⟨a, ha, ha1, ha2⟩⟩ := hOpp p (by omega)
  -- primes in `((p+1)² - (p+1), (p+1)²)` and `((p+1)², (p+1)² + (p+1))`
  obtain ⟨⟨b, hb, hb1, hb2⟩, ⟨c, hc, hc1, hc2⟩⟩ := hOpp (p + 1) (by omega)
  -- a prime in `(q² - q, q²)`
  obtain ⟨⟨d, hd, hd1, hd2⟩, -⟩ := hOpp q (by omega)
  have hexp : (p + 1) * (p + 1) = p * p + 2 * p + 1 := by ring
  have hbb : (p + 1) * (p + 1) - (p + 1) = p * p + p := by omega
  have hqq : q * q - q = q * (q - 1) := by
    cases q with
    | zero => simp
    | succ n => simp [Nat.succ_mul, Nat.mul_succ]
  have hmul : (p + 2) * (p + 1) ≤ q * (q - 1) := Nat.mul_le_mul (by omega) (by omega)
  have hdd : p * p + 3 * p + 2 ≤ q * q - q := by nlinarith [hqq, hmul]
  exact four_le_primesBetween ha hb hc hd ha1 (by omega) (by omega) (by omega) hd2

/-- **Brocard's gap conjecture** (conditional reduction): assuming Oppermann's conjecture,
for every `n ≥ 1` there are at least four primes strictly between the squares of the
`n`-th and `(n+1)`-st primes (indices are 0-based, so `Nat.nth Nat.Prime 1 = 3`). -/
theorem BrocardGapConjecture (hOpp : OppermannConjecture) (n : ℕ) (hn : 1 ≤ n) :
    4 ≤ primesBetween (Nat.nth Nat.Prime n * Nat.nth Nat.Prime n)
      (Nat.nth Nat.Prime (n + 1) * Nat.nth Nat.Prime (n + 1)) := by
  have hinf := Nat.infinite_setOf_prime
  have hp : (Nat.nth Nat.Prime n).Prime := Nat.prime_nth_prime n
  have hq : (Nat.nth Nat.Prime (n + 1)).Prime := Nat.prime_nth_prime (n + 1)
  have hlt : Nat.nth Nat.Prime n < Nat.nth Nat.Prime (n + 1) :=
    (Nat.nth_lt_nth hinf).mpr (by omega)
  have h0 : Nat.nth Nat.Prime 0 < Nat.nth Nat.Prime n := (Nat.nth_lt_nth hinf).mpr (by omega)
  rw [Nat.nth_prime_zero_eq_two] at h0
  have hp3 : 3 ≤ Nat.nth Nat.Prime n := by omega
  exact four_le_primesBetween_sq hOpp hp hq hp3 hlt

/-- Unconditional check of the first instance: there are at least four primes strictly
between `3² = 9` and `5² = 25`. -/
lemma four_le_primesBetween_nine_twentyfive : 4 ≤ primesBetween 9 25 := by
  decide

/-- Unconditional first case `n = 1` of the Brocard gap statement: at least four primes lie
strictly between the squares of the second and third primes (`3² = 9` and `5² = 25`).
This instance needs no hypothesis. -/
theorem brocardGap_one :
    4 ≤ primesBetween (Nat.nth Nat.Prime 1 * Nat.nth Nat.Prime 1)
      (Nat.nth Nat.Prime 2 * Nat.nth Nat.Prime 2) := by
  rw [Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five]
  exact four_le_primesBetween_nine_twentyfive

end Brockian.BrocardGap

