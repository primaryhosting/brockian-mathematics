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

open Finset

namespace Brockian.PracticalNumbers

/-- A positive natural number `n` is *practical* when every `m ≤ n` can be written as a sum
of distinct divisors of `n`. -/

lemma practical_mul {n d : ℕ} (hn : Practical n) (hd : 0 < d)
    (hdle : d ≤ 1 + ∑ y ∈ n.divisors, y) : Practical (n * d) := by
  obtain ⟨hn0, hrep⟩ := hn
  refine ⟨Nat.mul_pos hn0 hd, ?_⟩
  intro m hm
  have hqle : m / d ≤ n := by
    calc m / d ≤ (n * d) / d := Nat.div_le_div_right hm
    _ = n := Nat.mul_div_cancel _ hd
  obtain ⟨S1, hS1, hsum1⟩ := hrep (m / d) hqle
  have hrle : m % d ≤ ∑ y ∈ n.divisors, y := by
    have := Nat.mod_lt m hd
    omega
  obtain ⟨S2, hS2, hsum2⟩ := exists_subset_sum_of_practical ⟨hn0, hrep⟩ (m % d) hrle
  have hS1pos : ∀ e ∈ S1, 1 ≤ e := by
    intro e he
    have he' := Nat.mem_divisors.mp (hS1 he)
    refine Nat.one_le_iff_ne_zero.mpr ?_
    rintro rfl
    exact absurd (Nat.eq_zero_of_zero_dvd he'.1) hn0.ne'
  have hdisj : Disjoint (S1.image (fun e => d * e)) S2 := by
    rw [Finset.disjoint_left]
    intro u hu hu2
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hu
    have h1 : d ≤ d * e := Nat.le_mul_of_pos_right d (hS1pos e he)
    have h2 : d * e ≤ ∑ y ∈ S2, y :=
      Finset.single_le_sum (f := fun y => y) (fun i _ => Nat.zero_le i) hu2
    rw [hsum2] at h2
    have := Nat.mod_lt m hd
    omega
  refine ⟨(S1.image (fun e => d * e)) ∪ S2, ?_, ?_⟩
  · intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hu
      have he' := Nat.mem_divisors.mp (hS1 he)
      refine Nat.mem_divisors.mpr ⟨?_, (Nat.mul_pos hn0 hd).ne'⟩
      obtain ⟨k, hk⟩ := he'.1
      exact ⟨k, by rw [hk]; ring⟩
    · have hu' := Nat.mem_divisors.mp (hS2 hu)
      exact Nat.mem_divisors.mpr ⟨hu'.1.trans (Dvd.intro d rfl), (Nat.mul_pos hn0 hd).ne'⟩
  · rw [Finset.sum_union hdisj, Finset.sum_image (by
      intro a _ b _ hab
      exact Nat.eq_of_mul_eq_mul_left hd hab), hsum2, ← Finset.mul_sum, hsum1]
    exact Nat.div_add_mod m d

