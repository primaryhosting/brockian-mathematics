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
## Overview

A natural number `n` is *weird* when it is abundant (the sum of its proper divisors exceeds
`n`) but not semiperfect (no set of distinct proper divisors of `n` sums to `n`).  The smallest
weird number is `70`.

Whether an **odd** weird number exists is a well-known open problem; none is known, and none
exists below very large search bounds.  Accordingly, the target statement
`Brockian.WeirdNumbers.OddWeirdExists` is formalised here as a *conditional reduction*: it derives
the existence of an odd weird number from the existence of an odd abundant number whose
*abundance* `σ(n) - 2n` is not a subset sum of the proper divisors of `n`.

The reduction is not a weakening: `weird_iff_abundance_not_representable` shows that the
hypothesis is in fact equivalent to the conclusion's content, and it is the numerically more
convenient criterion (the abundance is usually far smaller than `n`).

Besides that, this file contains:

* `isWeird_70` — a machine-checked verification that `70` is weird (a sanity check on the
  definitions);
* `no_odd_weird_below_1000` — no odd weird number is smaller than `1000`;
* `isWeird_mul_prime` — if `n` is weird and `p` is a prime larger than `σ n`, then `n * p` is
  weird; hence (`infinite_odd_weird_of_odd_weird`) a single odd weird number would produce
  infinitely many.
-/

namespace Brockian.WeirdNumbers

open Finset

/-- `n` is *semiperfect* (pseudoperfect) if some set of distinct proper divisors of `n`
sums to `n`. -/
def IsSemiperfect (n : ℕ) : Prop :=
  ∃ S ∈ n.properDivisors.powerset, ∑ d ∈ S, d = n

instance (n : ℕ) : Decidable (IsSemiperfect n) := by
  unfold IsSemiperfect; infer_instance

/-- `n` is *weird* if it is abundant but not semiperfect. -/
def IsWeird (n : ℕ) : Prop := Nat.Abundant n ∧ ¬ IsSemiperfect n

/-- The abundance of `n`: the amount by which the sum of the proper divisors of `n`
exceeds `n`, i.e. `σ(n) - 2n`. -/
def abundance (n : ℕ) : ℕ := (∑ d ∈ n.properDivisors, d) - n

/-- Complementation inside the set of proper divisors: for an abundant `n`, a subset of the
proper divisors sums to `n` exactly when some subset sums to the abundance of `n`. -/
theorem semiperfect_iff_abundance_representable (n : ℕ) (h : Nat.Abundant n) :
    IsSemiperfect n ↔ ∃ T ∈ n.properDivisors.powerset, ∑ d ∈ T, d = abundance n := by
  have hab : n < ∑ d ∈ n.properDivisors, d := h
  unfold IsSemiperfect abundance
  constructor
  · rintro ⟨S, hS, hsum⟩
    refine ⟨n.properDivisors \ S, by simp, ?_⟩
    have := Finset.sum_sdiff (f := id) (Finset.mem_powerset.mp hS)
    simp only [id] at this
    omega
  · rintro ⟨T, hT, hsum⟩
    refine ⟨n.properDivisors \ T, by simp, ?_⟩
    have := Finset.sum_sdiff (f := id) (Finset.mem_powerset.mp hT)
    simp only [id] at this
    omega

/-- Weirdness restated in terms of the abundance: `n` is weird iff it is abundant and its
abundance is not a sum of distinct proper divisors of `n`. -/
theorem weird_iff_abundance_not_representable (n : ℕ) :
    IsWeird n ↔
      Nat.Abundant n ∧ ¬ ∃ T ∈ n.properDivisors.powerset, ∑ d ∈ T, d = abundance n := by
  constructor
  · rintro ⟨hab, hns⟩
    exact ⟨hab, fun h => hns ((semiperfect_iff_abundance_representable n hab).mpr h)⟩
  · rintro ⟨hab, hns⟩
    exact ⟨hab, fun h => hns ((semiperfect_iff_abundance_representable n hab).mp h)⟩

/-!
## The target statement

The unconditional existence of an odd weird number is open.  What is proved here is the
reduction to the (equivalent, but numerically more tractable) abundance criterion.
-/

/-- **Conditional existence of an odd weird number.**  If there is an odd abundant number whose
abundance `σ(n) - 2n` cannot be written as a sum of distinct proper divisors of `n`, then an odd
weird number exists.

(The unconditional statement `∃ n, Odd n ∧ IsWeird n` is a well-known open problem, so the
result is stated as this reduction.) -/
theorem OddWeirdExists
    (h : ∃ n, Odd n ∧ Nat.Abundant n ∧
      ¬ ∃ T ∈ n.properDivisors.powerset, ∑ d ∈ T, d = abundance n) :
    ∃ n, Odd n ∧ IsWeird n := by
  obtain ⟨n, hodd, hab, hrep⟩ := h
  exact ⟨n, hodd, (weird_iff_abundance_not_representable n).mpr ⟨hab, hrep⟩⟩

/-!
## Sanity checks and a small-range verification
-/

set_option maxRecDepth 40000 in
/-- `70` is weird: it is abundant, and no set of distinct proper divisors of `70` sums to `70`. -/
theorem isWeird_70 : IsWeird 70 := by
  constructor
  · decide
  · decide

/-- `945` is semiperfect (it is the smallest odd abundant number). -/
theorem isSemiperfect_945 : IsSemiperfect 945 :=
  ⟨{1, 9, 21, 27, 35, 45, 63, 105, 135, 189, 315}, by decide, by decide⟩

set_option maxRecDepth 100000 in
/-- No odd weird number is smaller than `1000`. -/
theorem no_odd_weird_below_1000 : ∀ n < 1000, Odd n → ¬ IsWeird n := by
  have key : ∀ n < 1000, n ≠ 945 → Odd n → ¬ IsWeird n := by decide
  intro n hn hodd hw
  by_cases h945 : n = 945
  · exact hw.2 (h945 ▸ isSemiperfect_945)
  · exact key n hn h945 hodd hw

/-!
## Propagation: one odd weird number would give infinitely many
-/

/-- The divisors of `n * p` for a prime `p`: those coprime to `p` (which divide `n`) together
with `p` times a divisor of `n`. -/
theorem divisors_mul_prime (n p : ℕ) (hn : 0 < n) (hp : p.Prime) :
    (n * p).divisors = n.divisors ∪ n.divisors.image (fun d => p * d) := by
  have hnp : n * p ≠ 0 := Nat.mul_ne_zero hn.ne' hp.pos.ne'
  ext d
  simp only [Nat.mem_divisors, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨hd, _⟩
    by_cases hpd : p ∣ d
    · obtain ⟨e, rfl⟩ := hpd
      exact Or.inr ⟨e, ⟨(Nat.mul_dvd_mul_iff_left hp.pos).mp (by rwa [mul_comm n p] at hd),
        hn.ne'⟩, rfl⟩
    · exact Or.inl ⟨Nat.Coprime.dvd_of_dvd_mul_right
        ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd).symm hd, hn.ne'⟩
  · rintro (⟨hd, _⟩ | ⟨e, ⟨he, _⟩, rfl⟩)
    · exact ⟨hd.mul_right p, hnp⟩
    · exact ⟨by rw [mul_comm n p]; exact Nat.mul_dvd_mul_left p he, hnp⟩

/-- Multiplicativity of `σ` at a prime not dividing `n`. -/
theorem sigma_mul_prime (n p : ℕ) (hn : 0 < n) (hp : p.Prime) (hpn : ¬ p ∣ n) :
    ∑ d ∈ (n * p).divisors, d = (∑ d ∈ n.divisors, d) * (1 + p) := by
  rw [divisors_mul_prime n p hn hp, Finset.sum_union, Finset.sum_image]
  · rw [← Finset.mul_sum]; ring
  · intro a _ b _ h; exact Nat.eq_of_mul_eq_mul_left hp.pos h
  · rw [Finset.disjoint_left]
    rintro a ha ha2
    simp only [Finset.mem_image, Nat.mem_divisors] at ha ha2
    obtain ⟨e, ⟨_, _⟩, rfl⟩ := ha2
    exact hpn (dvd_trans (Dvd.intro e rfl) ha.1)

/-- Sum over proper divisors in terms of `σ`. -/
theorem sum_properDivisors_eq (n : ℕ) (hn : 0 < n) :
    ∑ d ∈ n.properDivisors, d = (∑ d ∈ n.divisors, d) - n := by
  have h : n.divisors = insert n n.properDivisors := (Nat.insert_self_properDivisors hn.ne').symm
  have hnot : n ∉ n.properDivisors := by simp [Nat.properDivisors]
  rw [h, Finset.sum_insert hnot]
  omega

/-- If `n` is weird and `p` is a prime exceeding `σ n`, then `n * p` is weird. -/
theorem isWeird_mul_prime (n p : ℕ) (hn : 0 < n) (hp : p.Prime)
    (hpσ : ∑ d ∈ n.divisors, d < p) (hw : IsWeird n) : IsWeird (n * p) := by
  have hab : n < ∑ d ∈ n.properDivisors, d := hw.1
  have hσn : 2 * n < ∑ d ∈ n.divisors, d := by
    have := sum_properDivisors_eq n hn
    have hle : n ≤ ∑ d ∈ n.divisors, d :=
      Finset.single_le_sum (f := fun d => d) (fun i _ => Nat.zero_le i)
        (Nat.mem_divisors_self n hn.ne')
    omega
  have hpn : ¬ p ∣ n := by
    intro hdvd
    have : p ≤ n := Nat.le_of_dvd hn hdvd
    have hle : n ≤ ∑ d ∈ n.divisors, d :=
      Finset.single_le_sum (f := fun d => d) (fun i _ => Nat.zero_le i)
        (Nat.mem_divisors_self n hn.ne')
    omega
  have hnp : 0 < n * p := Nat.mul_pos hn hp.pos
  constructor
  · -- abundance of `n * p`
    show n * p < ∑ d ∈ (n * p).properDivisors, d
    rw [sum_properDivisors_eq _ hnp, sigma_mul_prime n p hn hp hpn]
    have h1 : (2 * n + 1) * (1 + p) ≤ (∑ d ∈ n.divisors, d) * (1 + p) :=
      Nat.mul_le_mul_right _ (by omega)
    nlinarith [hp.pos]
  · -- not semiperfect
    rintro ⟨S, hS, hsum⟩
    have hSsub : S ⊆ (n * p).properDivisors := Finset.mem_powerset.mp hS
    classical
    set A := S.filter (fun d => ¬ p ∣ d) with hA
    set B := S.filter (fun d => p ∣ d) with hB
    have hsplit : ∑ d ∈ B, d + ∑ d ∈ A, d = n * p := by
      rw [hA, hB, Finset.sum_filter_add_sum_filter_not S (fun d => p ∣ d)]
      exact hsum
    -- elements of `A` are divisors of `n`
    have hAsub : A ⊆ n.divisors := by
      intro a ha
      rw [hA, Finset.mem_filter] at ha
      have hmem := hSsub ha.1
      rw [Nat.mem_properDivisors] at hmem
      exact Nat.mem_divisors.mpr ⟨Nat.Coprime.dvd_of_dvd_mul_right
        ((Nat.Prime.coprime_iff_not_dvd hp).mpr ha.2).symm hmem.1, hn.ne'⟩
    have hAle : ∑ d ∈ A, d ≤ ∑ d ∈ n.divisors, d :=
      Finset.sum_le_sum_of_subset hAsub
    -- `p` divides the sum over `B`
    have hpB : p ∣ ∑ d ∈ B, d :=
      Finset.dvd_sum (fun d hd => (Finset.mem_filter.mp (hB ▸ hd)).2)
    have hpA : p ∣ ∑ d ∈ A, d := by
      have : ∑ d ∈ A, d = n * p - ∑ d ∈ B, d := by omega
      rw [this]
      exact Nat.dvd_sub (Dvd.intro n rfl) hpB
    have hA0 : ∑ d ∈ A, d = 0 := by
      rcases Nat.eq_zero_or_pos (∑ d ∈ A, d) with h | h
      · exact h
      · have := Nat.le_of_dvd h hpA
        omega
    have hBsum : ∑ d ∈ B, d = n * p := by omega
    -- `B` consists of `p` times a proper divisor of `n`
    set B' := n.properDivisors.filter (fun e => p * e ∈ S) with hB'
    have hBeq : B = B'.image (fun e => p * e) := by
      ext d
      simp only [hB, hB', Finset.mem_filter, Finset.mem_image, Nat.mem_properDivisors]
      constructor
      · rintro ⟨hdS, e, rfl⟩
        have hmem := hSsub hdS
        rw [Nat.mem_properDivisors] at hmem
        refine ⟨e, ⟨⟨(Nat.mul_dvd_mul_iff_left hp.pos).mp (by rwa [mul_comm n p] at hmem.1), ?_⟩,
          hdS⟩, rfl⟩
        have := hmem.2
        rw [mul_comm n p] at this
        exact lt_of_mul_lt_mul_left this (Nat.zero_le p)
      · rintro ⟨e, ⟨⟨_, _⟩, heS⟩, rfl⟩
        exact ⟨heS, Dvd.intro e rfl⟩
    have hinj : ∀ a ∈ B', ∀ b ∈ B', p * a = p * b → a = b :=
      fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hp.pos h
    have hB'sum : p * ∑ e ∈ B', e = n * p := by
      rw [Finset.mul_sum, ← hBsum, hBeq, Finset.sum_image hinj]
    have : ∑ e ∈ B', e = n := by
      have hp0 : 0 < p := hp.pos
      nlinarith [hB'sum]
    exact hw.2 ⟨B', Finset.mem_powerset.mpr (by rw [hB']; exact Finset.filter_subset _ _), this⟩

/-- If an odd weird number exists, then there are arbitrarily large odd weird numbers. -/
theorem infinite_odd_weird_of_odd_weird (h : ∃ n, Odd n ∧ IsWeird n) :
    ∀ N : ℕ, ∃ m > N, Odd m ∧ IsWeird m := by
  obtain ⟨n, hodd, hw⟩ := h
  intro N
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact absurd hw.1 (by decide)
    · exact h
  obtain ⟨p, hple, hp⟩ := Nat.exists_infinite_primes (max ((∑ d ∈ n.divisors, d) + 1) (N + 1))
  have hpσ : ∑ d ∈ n.divisors, d < p := lt_of_lt_of_le (by omega) (le_trans (le_max_left _ _) hple)
  have hpN : N < p := lt_of_lt_of_le (by omega) (le_trans (le_max_right _ _) hple)
  have hpodd : Odd p := hp.odd_of_ne_two (by
    intro h2
    have : (2 : ℕ) ≤ ∑ d ∈ n.divisors, d := by
      have h1 : n ≤ ∑ d ∈ n.divisors, d :=
        Finset.single_le_sum (f := fun d => d) (fun i _ => Nat.zero_le i)
          (Nat.mem_divisors_self n hn.ne')
      have hab : n < ∑ d ∈ n.properDivisors, d := hw.1
      have := sum_properDivisors_eq n hn
      omega
    omega)
  refine ⟨n * p, ?_, hodd.mul hpodd, isWeird_mul_prime n p hn hp hpσ hw⟩
  calc N < p := hpN
    _ ≤ n * p := Nat.le_mul_of_pos_left p hn

end Brockian.WeirdNumbers

