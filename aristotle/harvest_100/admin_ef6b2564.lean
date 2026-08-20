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

open Finset

/-!
## Status

`OddWeirdExists` (the existence of an odd weird number) is an open problem, and is **not** proved
here. What is proved, axiom-cleanly:

* `oddWeirdExists_iff` — an elementary restatement of the target;
* `pseudoperfect_mul_left`, `pseudoperfect_of_dvd`, `not_pseudoperfect_of_dvd_of_weird` — every
  multiple of a pseudoperfect number is pseudoperfect, hence no divisor of a weird number is
  pseudoperfect;
* `not_dvd_945_of_weird`, `not_dvd_of_perfect_of_weird`, `not_perfect_of_weird` — concrete
  consequences (e.g. no weird number is a multiple of `945`, the smallest odd abundant number);
* `weird_mul_prime` — if `n` is weird and `p` is a prime exceeding the sum of the divisors of `n`,
  then `n * p` is weird;
* `oddWeirdExists_iff_infinite` — the conditional reduction: one odd weird number would already
  force infinitely many;
* `even_weird_exists` — the even case, via Mathlib's `Nat.weird_seventy`.

The relevant existing Mathlib material is `Mathlib/NumberTheory/FactorisationProperties.lean`
(`Nat.Abundant`, `Nat.Pseudoperfect`, `Nat.Weird`, `Nat.Abundant.of_dvd`, `Nat.weird_seventy`);
no Mathlib lemma closes the target itself.
-/

namespace Brockian.WeirdNumbers

/-- The Brockian statement "an odd weird number exists".

A natural number is *weird* (`Nat.Weird`, from Mathlib's
`Mathlib/NumberTheory/FactorisationProperties.lean`) when it is abundant (the sum of its proper
divisors exceeds it) but not pseudoperfect (no subset of its proper divisors sums to it).
Whether an odd weird number exists is an open problem; this file therefore develops
Lean-checked reductions and partial results around the statement. -/
def OddWeirdExists : Prop := ∃ n : ℕ, Odd n ∧ n.Weird

/-- Unfolding of `OddWeirdExists` into elementary arithmetic terms. -/
theorem oddWeirdExists_iff :
    OddWeirdExists ↔
      ∃ n : ℕ, Odd n ∧ n < ∑ i ∈ n.properDivisors, i ∧
        ∀ s ⊆ n.properDivisors, ∑ i ∈ s, i ≠ n := by
  constructor
  · rintro ⟨n, hodd, ⟨hab, hps⟩⟩
    refine ⟨n, hodd, hab, ?_⟩
    rcases Nat.not_pseudoperfect_iff_forall.1 hps with h | h
    · simp [Nat.Abundant, h] at hab
    · exact h
  · rintro ⟨n, hodd, hab, h⟩
    exact ⟨n, hodd, hab, Nat.not_pseudoperfect_iff_forall.2 (Or.inr h)⟩

/-- Multiples of pseudoperfect numbers are pseudoperfect. -/
theorem pseudoperfect_mul_left {m k : ℕ} (hm : m.Pseudoperfect) (hk : k ≠ 0) :
    (k * m).Pseudoperfect := by
  obtain ⟨hm0, s, hs, hsum⟩ := hm
  have hk0 : 0 < k := Nat.pos_of_ne_zero hk
  refine ⟨by positivity, s.image (fun d => k * d), ?_, ?_⟩
  · intro x hx
    simp only [mem_image] at hx
    obtain ⟨d, hd, rfl⟩ := hx
    have hd' := hs hd
    rw [Nat.mem_properDivisors] at hd' ⊢
    exact ⟨mul_dvd_mul_left k hd'.1, mul_lt_mul_of_pos_left hd'.2 hk0⟩
  · rw [sum_image (by intro x _ y _ h; exact Nat.eq_of_mul_eq_mul_left hk0 h),
      ← Finset.mul_sum, hsum]

/-- A number with a pseudoperfect divisor is pseudoperfect. -/
theorem pseudoperfect_of_dvd {m n : ℕ} (hm : m.Pseudoperfect) (hd : m ∣ n) (hn : n ≠ 0) :
    n.Pseudoperfect := by
  obtain ⟨k, rfl⟩ := hd
  have hk : k ≠ 0 := by rintro rfl; simp at hn
  rw [mul_comm]
  exact pseudoperfect_mul_left hm hk

/-- No divisor of a weird number is pseudoperfect. -/
theorem not_pseudoperfect_of_dvd_of_weird {n m : ℕ} (hn : n.Weird) (hd : m ∣ n) :
    ¬ m.Pseudoperfect := by
  intro hm
  have hn0 : n ≠ 0 := by rintro rfl; exact Nat.not_abundant_zero hn.1
  exact hn.2 (pseudoperfect_of_dvd hm hd hn0)

/-- `945`, the smallest odd abundant number, is pseudoperfect. -/
theorem pseudoperfect_945 : Nat.Pseudoperfect 945 := by
  refine ⟨by norm_num, {315, 189, 135, 105, 63, 45, 35, 27, 21, 9, 1}, by decide, by decide⟩

/-- Partial result: no weird number is a multiple of `945` (in particular no odd weird number is). -/
theorem not_dvd_945_of_weird {n : ℕ} (hn : n.Weird) : ¬ (945 ∣ n) :=
  fun hd => not_pseudoperfect_of_dvd_of_weird hn hd pseudoperfect_945

/-- A weird number is not perfect. -/
theorem not_perfect_of_weird {n : ℕ} (hn : n.Weird) : ¬ n.Perfect :=
  fun hper => hn.2 hper.pseudoperfect

/-- No perfect number divides a weird number. -/
theorem not_dvd_of_perfect_of_weird {n m : ℕ} (hn : n.Weird) (hm : m.Perfect) : ¬ (m ∣ n) :=
  fun hd => not_pseudoperfect_of_dvd_of_weird hn hd hm.pseudoperfect

/-- If `n` is weird and `p` is a prime larger than the sum of the divisors of `n`,
then `n * p` is weird. -/
theorem weird_mul_prime {n p : ℕ} (hn : n.Weird) (hp : p.Prime)
    (hlt : ∑ i ∈ n.divisors, i < p) : (n * p).Weird := by
  obtain ⟨hab, hps⟩ := hn
  have hn0 : n ≠ 0 := by rintro rfl; simp [Nat.Abundant] at hab
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hppos : 0 < p := hp.pos
  have hnp0 : n * p ≠ 0 := Nat.mul_ne_zero hn0 hp.ne_zero
  refine ⟨Nat.Abundant.of_dvd hab (dvd_mul_right n p) hnp0, ?_⟩
  rintro ⟨-, s, hs, hsum⟩
  set s₁ := s.filter (fun d => ¬ p ∣ d) with hs₁
  set s₂ := s.filter (fun d => p ∣ d) with hs₂
  have hsplit : ∑ i ∈ s₂, i + ∑ i ∈ s₁, i = n * p := by
    rw [hs₁, hs₂, Finset.sum_filter_add_sum_filter_not]; exact hsum
  have hs₁div : s₁ ⊆ n.divisors := by
    intro d hd
    rw [hs₁, mem_filter] at hd
    obtain ⟨hd, hpd⟩ := hd
    have hd' := hs hd
    rw [Nat.mem_properDivisors] at hd'
    have hcop : Nat.Coprime d p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hpd).symm
    exact Nat.mem_divisors.2 ⟨hcop.dvd_of_dvd_mul_right hd'.1, hn0⟩
  have hs₁lt : ∑ i ∈ s₁, i < p :=
    lt_of_le_of_lt (Finset.sum_le_sum_of_subset hs₁div) hlt
  set t := s₂.image (fun d => d / p) with ht
  have hinj : Set.InjOn (fun d => d / p) s₂ := by
    intro a ha b hb hab'
    rw [hs₂, mem_coe, mem_filter] at ha hb
    simp only at hab'
    rw [← Nat.div_mul_cancel ha.2, ← Nat.div_mul_cancel hb.2, hab']
  have hsum₂ : ∑ i ∈ s₂, i = p * ∑ e ∈ t, e := by
    rw [ht, Finset.sum_image hinj, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro d hd
    rw [hs₂, mem_filter] at hd
    exact (Nat.mul_div_cancel' hd.2).symm
  have htsub : t ⊆ n.properDivisors := by
    intro e he
    rw [ht, mem_image] at he
    obtain ⟨d, hd, rfl⟩ := he
    rw [hs₂, mem_filter] at hd
    obtain ⟨hd, hpd⟩ := hd
    have hd' := hs hd
    rw [Nat.mem_properDivisors] at hd'
    obtain ⟨hdvd, hltd⟩ := hd'
    obtain ⟨e, rfl⟩ := hpd
    rw [Nat.mul_div_cancel_left _ hppos, Nat.mem_properDivisors]
    rw [mul_comm n p] at hdvd hltd
    exact ⟨(mul_dvd_mul_iff_left hp.ne_zero).1 hdvd, lt_of_mul_lt_mul_left hltd (Nat.zero_le p)⟩
  have hpdvd : p ∣ ∑ i ∈ s₁, i := by
    have h1 : ∑ i ∈ s₁, i = n * p - p * ∑ e ∈ t, e := by omega
    rw [h1]
    exact Nat.dvd_sub (Dvd.intro_left n rfl) (Dvd.intro _ rfl)
  have hzero : ∑ i ∈ s₁, i = 0 := by
    rcases Nat.eq_zero_or_pos (∑ i ∈ s₁, i) with h | h
    · exact h
    · exact absurd (Nat.le_of_dvd h hpdvd) (by omega)
  have hT : ∑ e ∈ t, e = n := by
    have h2 : p * ∑ e ∈ t, e = n * p := by omega
    exact Nat.eq_of_mul_eq_mul_left hppos (h2.trans (mul_comm n p))
  exact hps ⟨hnpos, t, htsub, hT⟩

/-- Conditional reduction: if one odd weird number exists, there are infinitely many. -/
theorem oddWeirdExists_iff_infinite :
    OddWeirdExists ↔ {n : ℕ | Odd n ∧ n.Weird}.Infinite := by
  constructor
  · rintro ⟨n, hodd, hw⟩
    have hn0 : n ≠ 0 := by rintro rfl; simp [Nat.Weird, Nat.Abundant] at hw
    rw [Set.infinite_iff_exists_gt]
    intro a
    obtain ⟨p, hple, hp⟩ :=
      Nat.exists_infinite_primes (max (a + 1) (max ((∑ i ∈ n.divisors, i) + 1) 3))
    have h1 : a < p := by omega
    have h2 : ∑ i ∈ n.divisors, i < p := by omega
    refine ⟨n * p, ⟨hodd.mul (hp.odd_of_ne_two (by omega)), weird_mul_prime hw hp h2⟩, ?_⟩
    calc a < p := h1
      _ ≤ n * p := Nat.le_mul_of_pos_left p (Nat.pos_of_ne_zero hn0)
  · intro h
    obtain ⟨n, hn⟩ := h.nonempty
    exact ⟨n, hn.1, hn.2⟩

/-- The even case is settled: `70` is weird (Mathlib's `Nat.weird_seventy`). -/
theorem even_weird_exists : ∃ n : ℕ, Even n ∧ n.Weird :=
  ⟨70, by decide, Nat.weird_seventy⟩

end Brockian.WeirdNumbers

