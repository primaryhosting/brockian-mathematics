import RequestProject.Defs

/-!
# The Bonferroni / Brun truncation inequality

Truncating the inclusion–exclusion sum at an even level `t` gives an upper bound for the
sifted count.
-/

namespace Brun

open Finset

/-- Partial alternating sums of binomial coefficients. -/

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
