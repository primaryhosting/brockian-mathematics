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
# Practical Twin Infinitude
Category: Brockian Conjecture
Target: Brockian.PracticalNumbers.PracticalTwinInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
## Practical numbers and practical twins

A positive integer `n` is *practical* if every `m ≤ σ(n)` is a sum of distinct divisors of `n`.
The *practical twin* problem asks whether there are infinitely many `n` such that both `n` and
`n + 2` are practical (this is a known but genuinely deep statement, proved by sieve methods;
no unconditional proof is formalised here).

This file develops:

* `IsPractical`, `DivisorComplete` and the equivalence `isPractical_iff_divisorComplete`
  between practicality and the elementary divisor-chain criterion "every divisor is at most one
  more than the sum of the smaller divisors";
* decidability of the criterion, and explicit practical twin pairs up to `(8190, 8192)`;
* `isPractical_two_pow`, `infinite_practical`: powers of two are practical, so there are
  infinitely many practical numbers;
* `isPractical_mul_prime`: the coprime case of Stewart's multiplication theorem, and the family
  `isPractical_prime_mul_two_pow`;
* `practicalTwinConjecture_iff` and `PracticalTwinInfinitude`: a Lean-checked reduction of the
  practical twin conjecture to the elementary criterion.
-/

set_option maxRecDepth 10000

open Finset

namespace Brockian.PracticalNumbers

/-- A positive integer `n` is *practical* if every `m ≤ σ(n)` is the sum of a set of
pairwise distinct divisors of `n`. -/

theorem isPractical_mul_prime {n p : ℕ} (hn : IsPractical n) (hp : p.Prime) (hpn : ¬ p ∣ n)
    (hple : p ≤ 1 + ∑ d ∈ n.divisors, d) : IsPractical (p * n) := by
  obtain ⟨hpos, hrep⟩ := hn
  set D := n.divisors with hD
  set sig := ∑ d ∈ D, d with hsig
  have hdisj : Disjoint D (D.image (p * ·)) := by
    rw [Finset.disjoint_right]
    rintro x hx hxD
    simp only [Finset.mem_image] at hx
    obtain ⟨d, hd, rfl⟩ := hx
    exact hpn (dvd_trans (Dvd.intro d rfl) (Nat.mem_divisors.1 hxD).1)
  have hdiv : (p * n).divisors = D ∪ D.image (p * ·) := divisors_mul_prime p n hp
  have hinj : Set.InjOn (p * ·) D := fun a _ b _ h => by
    simpa [Nat.mul_left_cancel_iff hp.pos] using h
  have hsum : ∑ d ∈ (p * n).divisors, d = sig + p * sig := by
    rw [hdiv, Finset.sum_union hdisj, Finset.sum_image (fun a ha b hb h => hinj ha hb h),
      ← Finset.mul_sum]
  refine ⟨Nat.mul_pos hp.pos hpos, ?_⟩
  intro m hm
  rw [hsum] at hm
  have hA1 : p * (m / p) ≤ m := by rw [Nat.mul_comm]; exact Nat.div_mul_le_self m p
  have hA2 : m = p * (m / p) + m % p := (Nat.div_add_mod m p).symm
  have hA3 : m % p < p := Nat.mod_lt _ hp.pos
  obtain ⟨q, hqs, hpq, hr⟩ : ∃ q, q ≤ sig ∧ p * q ≤ m ∧ m - p * q ≤ sig := by
    rcases le_total (m / p) sig with h | h
    · exact ⟨m / p, h, hA1, by omega⟩
    · refine ⟨sig, le_rfl, le_trans (Nat.mul_le_mul_left p h) hA1, ?_⟩
      have : p * sig ≤ p * (m / p) := Nat.mul_le_mul_left p h
      omega
  obtain ⟨A, hA, hAsum⟩ := hrep q hqs
  obtain ⟨B, hB, hBsum⟩ := hrep (m - p * q) hr
  refine ⟨B ∪ A.image (p * ·), ?_, ?_⟩
  · rw [hdiv]
    exact Finset.union_subset_union hB (Finset.image_subset_image hA)
  · have hd2 : Disjoint B (A.image (p * ·)) :=
      Finset.disjoint_of_subset_left hB (Finset.disjoint_of_subset_right
        (Finset.image_subset_image hA) hdisj)
    rw [Finset.sum_union hd2, Finset.sum_image (fun a ha b hb h => hinj (hA ha) (hA hb) h),
      ← Finset.mul_sum, hAsum, hBsum]
    omega

/-- The sum of the divisors of `2 ^ a`. -/
