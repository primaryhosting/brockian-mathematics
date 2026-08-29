import RequestProject.Defs

/-!
# The Bonferroni / Brun truncation inequality

Truncating the inclusion–exclusion sum at an even level `t` gives an upper bound for the
sifted count.
-/

namespace Brun

open Finset

/-- Partial alternating sums of binomial coefficients. -/
lemma alternating_choose_partial (s t : ℕ) :
    ∑ j ∈ range (t + 1), (-1 : ℝ) ^ j * (Nat.choose (s + 1) j) = (-1) ^ t * Nat.choose s t := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Finset.sum_range_succ, ih]
      have hp : (Nat.choose (s + 1) (t + 1) : ℝ) = Nat.choose s t + Nat.choose s (t + 1) := by
        rw [Nat.choose_succ_succ]
        push_cast
        ring
      rw [hp]
      ring

/-- The truncated alternating sum over subsets of a finset is at least the indicator of the
finset being empty, provided the truncation level is even. -/
lemma truncated_alternating_sum_nonneg {D : Finset ℕ} {t : ℕ} (ht : Even t) :
    (if D = ∅ then (1 : ℝ) else 0) ≤
      ∑ S ∈ D.powerset with S.card ≤ t, (-1 : ℝ) ^ S.card := by
  have hsplit : ∑ S ∈ D.powerset with S.card ≤ t, (-1 : ℝ) ^ S.card
      = ∑ j ∈ range (t + 1), (-1 : ℝ) ^ j * (Nat.choose D.card j) := by
    have : (D.powerset.filter (fun S => S.card ≤ t))
        = (range (t + 1)).biUnion (fun j => D.powersetCard j) := by
      ext S
      simp only [mem_filter, mem_powerset, mem_biUnion, mem_range, mem_powersetCard]
      constructor
      · rintro ⟨hS, hc⟩
        exact ⟨S.card, by lia, hS, rfl⟩
      · rintro ⟨j, hj, hS, rfl⟩
        exact ⟨hS, by lia⟩
    rw [this, Finset.sum_biUnion]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_congr rfl (fun S hS => by rw [(mem_powersetCard.1 hS).2]),
        Finset.sum_const, nsmul_eq_mul, card_powersetCard]
      ring
    · intro i _ j _ hij
      simp only [Finset.disjoint_left, mem_powersetCard]
      rintro S ⟨-, rfl⟩ ⟨-, h⟩
      exact hij h
  rw [hsplit]
  rcases Finset.eq_empty_or_nonempty D with rfl | hD
  · have : ∑ j ∈ range (t + 1), (-1 : ℝ) ^ j * (Nat.choose (∅ : Finset ℕ).card j) = 1 := by
      refine (Finset.sum_eq_single 0 ?_ ?_).trans (by simp)
      · intro b _ hb
        simp [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hb)]
      · simp
    rw [this]
    simp
  · have hc : D.card ≠ 0 := by simpa using hD.card_pos.ne'
    obtain ⟨s, hs⟩ : ∃ s, D.card = s + 1 := ⟨D.card - 1, by lia⟩
    rw [if_neg hD.ne_empty, hs, alternating_choose_partial]
    have : (0 : ℝ) ≤ (-1 : ℝ) ^ t := by
      rcases ht with ⟨u, hu⟩
      rw [hu, show u + u = 2 * u by ring, pow_mul]
      positivity
    positivity

/-- The main Bonferroni bound: the sifted count is at most the truncated inclusion–exclusion
sum. -/
theorem sifted_card_le_truncated (N z t : ℕ) (ht : Even t) :
    ((sifted N z).card : ℝ) ≤
      ∑ S ∈ (sievePrimes z).powerset with S.card ≤ t,
        (-1 : ℝ) ^ S.card * (sieveCount N S) := by
  have hrhs : ∑ S ∈ (sievePrimes z).powerset with S.card ≤ t,
        (-1 : ℝ) ^ S.card * (sieveCount N S)
      = ∑ n ∈ Icc 1 N, ∑ S ∈ (sievePrimes z).powerset with S.card ≤ t,
          (if ∀ p ∈ S, p ∣ n * (n + 2) then (-1 : ℝ) ^ S.card else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [sieveCount, ← Finset.sum_boole, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    split <;> simp
  rw [hrhs]
  have hlhs : ((sifted N z).card : ℝ)
      = ∑ n ∈ Icc 1 N, (if (sievePrimes z).filter (fun p => p ∣ n * (n + 2)) = ∅ then (1:ℝ) else 0)
      := by
    rw [sifted, ← Finset.sum_boole]
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 1
    simp [Finset.filter_eq_empty_iff]
  rw [hlhs]
  refine Finset.sum_le_sum fun n _ => ?_
  set D := (sievePrimes z).filter (fun p => p ∣ n * (n + 2)) with hD
  have hset : ((sievePrimes z).powerset.filter (fun S => S.card ≤ t)).filter
      (fun S => ∀ p ∈ S, p ∣ n * (n + 2)) = D.powerset.filter (fun S => S.card ≤ t) := by
    ext S
    simp only [mem_filter, mem_powerset, hD, Finset.subset_iff, mem_filter]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨fun _ hx => ⟨h1 hx, h3 _ hx⟩, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨fun _ hx => (h1 hx).1, h2⟩, fun _ hx => (h1 hx).2⟩
  calc (if D = ∅ then (1:ℝ) else 0)
      ≤ ∑ S ∈ D.powerset with S.card ≤ t, (-1 : ℝ) ^ S.card :=
        truncated_alternating_sum_nonneg ht
    _ = ∑ S ∈ (sievePrimes z).powerset with S.card ≤ t,
          (if ∀ p ∈ S, p ∣ n * (n + 2) then (-1 : ℝ) ^ S.card else 0) := by
        rw [← hset, Finset.sum_filter]

end Brun

import Mathlib

/-!
# Definitions for Brun's theorem

Basic objects used in the sieve-theoretic proof that the sum of the reciprocals of the twin
primes converges.
-/

namespace Brun

open Finset

/-- The odd primes `p ≤ z`; these are the primes we sift by. -/
def sievePrimes (z : ℕ) : Finset ℕ := (range (z + 1)).filter (fun p => p.Prime ∧ p ≠ 2)

/-- The twin primes `p ≤ N` (i.e. `p` and `p + 2` are both prime). -/
def twins (N : ℕ) : Finset ℕ := (range (N + 1)).filter (fun p => p.Prime ∧ (p + 2).Prime)

/-- The integers `1 ≤ n ≤ N` such that `n * (n + 2)` has no prime factor among `sievePrimes z`. -/
def sifted (N z : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun n => ∀ p ∈ sievePrimes z, ¬ p ∣ n * (n + 2))

/-- The number of `1 ≤ n ≤ N` such that every `p ∈ S` divides `n * (n + 2)`. -/
def sieveCount (N : ℕ) (S : Finset ℕ) : ℕ :=
  ((Icc 1 N).filter (fun n => ∀ p ∈ S, p ∣ n * (n + 2))).card

lemma mem_sievePrimes {z p : ℕ} : p ∈ sievePrimes z ↔ p ≤ z ∧ p.Prime ∧ p ≠ 2 := by
  simp [sievePrimes, Nat.lt_succ_iff, and_comm]

lemma sievePrimes_odd {z p : ℕ} (hp : p ∈ sievePrimes z) : Odd p := by
  rw [mem_sievePrimes] at hp
  exact hp.2.1.odd_of_ne_two hp.2.2

lemma three_le_of_mem_sievePrimes {z p : ℕ} (hp : p ∈ sievePrimes z) : 3 ≤ p := by
  rw [mem_sievePrimes] at hp
  rcases hp with ⟨-, hp, h2⟩
  have := hp.two_le
  rcases Nat.lt_or_ge p 3 with h | h
  · interval_cases p <;> simp_all
  · exact h

end Brun

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

