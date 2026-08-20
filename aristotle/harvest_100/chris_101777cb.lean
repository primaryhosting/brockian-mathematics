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
def IsPractical (n : ℕ) : Prop :=
  0 < n ∧ ∀ m ≤ ∑ d ∈ n.divisors, d, ∃ S ⊆ n.divisors, ∑ d ∈ S, d = m

/-- The elementary "complete divisor chain" criterion: every divisor of `n` is at most one
more than the sum of the strictly smaller divisors of `n`. -/
def DivisorComplete (n : ℕ) : Prop :=
  0 < n ∧ ∀ d ∈ n.divisors, d ≤ 1 + ∑ e ∈ n.divisors.filter (· < d), e

/-- `n` and `n + 2` are both practical: a *practical twin pair*. -/
def PracticalTwin (n : ℕ) : Prop := IsPractical n ∧ IsPractical (n + 2)

/-- Key combinatorial lemma: in a finite set of naturals in which every element is at most one
more than the sum of the strictly smaller elements, every value up to the total sum is a
subset sum. -/
theorem subsetSum_of_complete (S : Finset ℕ)
    (h : ∀ a ∈ S, a ≤ 1 + ∑ b ∈ S.filter (· < a), b) :
    ∀ m ≤ ∑ b ∈ S, b, ∃ T ⊆ S, ∑ b ∈ T, b = m := by
  induction S using Finset.strongInduction with
  | _ S ih =>
    intro m hm
    rcases S.eq_empty_or_nonempty with rfl | hne
    · refine ⟨∅, by simp, ?_⟩
      simp only [Finset.sum_empty] at hm
      simp [Nat.le_zero.1 hm]
    · set a := S.max' hne with ha_def
      have ha : a ∈ S := S.max'_mem hne
      have hfil : S.filter (· < a) = S.erase a := by
        ext x
        simp only [mem_filter, mem_erase]
        constructor
        · rintro ⟨hx, hlt⟩; exact ⟨by omega, hx⟩
        · rintro ⟨hne', hx⟩
          exact ⟨hx, lt_of_le_of_ne (S.le_max' x hx) hne'⟩
      have hss : S.erase a ⊂ S := erase_ssubset ha
      have hih : ∀ b ∈ S.erase a, b ≤ 1 + ∑ c ∈ (S.erase a).filter (· < b), c := by
        intro b hb
        have hb' : b ∈ S := mem_of_mem_erase hb
        have hfb : (S.erase a).filter (· < b) = S.filter (· < b) := by
          ext x
          simp only [mem_filter, mem_erase]
          constructor
          · rintro ⟨⟨_, hx⟩, hlt⟩; exact ⟨hx, hlt⟩
          · rintro ⟨hx, hlt⟩
            refine ⟨⟨?_, hx⟩, hlt⟩
            rintro rfl
            exact absurd (S.le_max' b hb') (by omega)
        rw [hfb]; exact h b hb'
      have hsum : ∑ b ∈ S, b = a + ∑ b ∈ S.erase a, b := (Finset.add_sum_erase S _ ha).symm
      by_cases hcase : m ≤ ∑ b ∈ S.erase a, b
      · obtain ⟨T, hT, hTsum⟩ := ih _ hss hih m hcase
        exact ⟨T, hT.trans (erase_subset _ _), hTsum⟩
      · push_neg at hcase
        have hale : a ≤ m := by
          have := h a ha
          rw [hfil] at this
          omega
        have hle : m - a ≤ ∑ b ∈ S.erase a, b := by omega
        obtain ⟨T, hT, hTsum⟩ := ih _ hss hih (m - a) hle
        have haT : a ∉ T := fun hc => (Finset.notMem_erase a S) (hT hc)
        refine ⟨insert a T, ?_, ?_⟩
        · intro x hx
          rcases mem_insert.1 hx with rfl | hx
          · exact ha
          · exact (hT.trans (erase_subset _ _)) hx
        · rw [Finset.sum_insert haT, hTsum]; omega

/-- The divisor-chain criterion characterises practical numbers. -/
theorem isPractical_iff_divisorComplete (n : ℕ) : IsPractical n ↔ DivisorComplete n := by
  constructor
  · rintro ⟨hpos, hrep⟩
    refine ⟨hpos, ?_⟩
    intro d hd
    by_contra hcon
    push_neg at hcon
    have hdn : d ∣ n := (Nat.mem_divisors.1 hd).1
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hdle : d ≤ n := Nat.le_of_dvd hpos hdn
    have hnmem : n ∈ n.divisors := Nat.mem_divisors_self n hpos.ne'
    have hnsum : n ≤ ∑ e ∈ n.divisors, e :=
      Finset.single_le_sum (f := fun e => e) (by intros; positivity) hnmem
    obtain ⟨T, hT, hTsum⟩ := hrep (d - 1) (by omega)
    have hTlt : T ⊆ n.divisors.filter (· < d) := by
      intro x hx
      have hx1 : x ≤ d - 1 :=
        hTsum ▸ Finset.single_le_sum (f := fun e => (e : ℕ)) (by intros; positivity) hx
      exact mem_filter.2 ⟨hT hx, by omega⟩
    have hfin : ∑ x ∈ T, x ≤ ∑ e ∈ n.divisors.filter (· < d), e := by
      simpa using Finset.sum_le_sum_of_subset (f := fun e => e) hTlt
    omega
  · rintro ⟨hpos, hcomp⟩
    exact ⟨hpos, subsetSum_of_complete _ hcomp⟩

instance : DecidablePred DivisorComplete := fun n => by
  unfold DivisorComplete; infer_instance

/-- Auxiliary: the sum of the first `i` powers of two. -/
theorem sum_range_two_pow (i : ℕ) : ∑ j ∈ Finset.range i, 2 ^ j = 2 ^ i - 1 := by
  induction i with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    ring_nf
    omega

theorem two_pow_divisorComplete (a : ℕ) : DivisorComplete (2 ^ a) := by
  refine ⟨Nat.two_pow_pos a, ?_⟩
  intro d hd
  rw [Nat.divisors_prime_pow Nat.prime_two] at hd ⊢
  simp only [Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk] at hd
  obtain ⟨i, hi, rfl⟩ := hd
  have hfil :
      (Finset.map ⟨fun x => 2 ^ x, fun x y h => by simpa using h⟩
          (Finset.range (a + 1))).filter (· < 2 ^ i)
        = Finset.map ⟨fun x => 2 ^ x, fun x y h => by simpa using h⟩ (Finset.range i) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨⟨j, hj, rfl⟩, hlt⟩
      exact ⟨j, (Nat.pow_lt_pow_iff_right (by norm_num)).1 hlt, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, by omega, rfl⟩, Nat.pow_lt_pow_right (by norm_num) hj⟩
  rw [hfil, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  rw [sum_range_two_pow]
  have : 1 ≤ 2 ^ i := Nat.one_le_two_pow
  omega

/-- Powers of two are practical. -/
theorem isPractical_two_pow (a : ℕ) : IsPractical (2 ^ a) :=
  (isPractical_iff_divisorComplete _).2 (two_pow_divisorComplete a)

/-- There are infinitely many practical numbers. -/
theorem infinite_practical (N : ℕ) : ∃ n > N, IsPractical n :=
  ⟨2 ^ (N + 1), by
      have h1 : N < 2 ^ N := Nat.lt_two_pow_self
      have h2 : 2 ^ N ≤ 2 ^ (N + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega, isPractical_two_pow _⟩

/-- The divisors of `p * n` for a prime `p`. -/
theorem divisors_mul_prime (p n : ℕ) (hp : p.Prime) :
    (p * n).divisors = n.divisors ∪ n.divisors.image (p * ·) := by
  rw [Nat.divisors_mul, hp.divisors]
  ext x
  simp [Finset.mem_mul, Nat.mem_divisors]

/-- Multiplying a practical number by a prime `p ∤ n` with `p ≤ σ(n) + 1` keeps it practical
(the coprime case of Stewart's theorem). -/
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
theorem sum_divisors_two_pow (a : ℕ) : ∑ d ∈ (2 ^ a).divisors, d = 2 ^ (a + 1) - 1 := by
  rw [Nat.divisors_prime_pow Nat.prime_two, Finset.sum_map]
  simpa using sum_range_two_pow (a + 1)

/-- An infinite family of practical numbers: `p * 2 ^ a` for any odd prime `p ≤ 2 ^ (a+1)`. -/
theorem isPractical_prime_mul_two_pow {p a : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hle : p ≤ 2 ^ (a + 1)) : IsPractical (p * 2 ^ a) := by
  refine isPractical_mul_prime (isPractical_two_pow a) hp ?_ ?_
  · intro hdvd
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd)
    exact hodd this
  · rw [sum_divisors_two_pow]
    have : 1 ≤ 2 ^ (a + 1) := Nat.one_le_two_pow
    omega

/-- Explicit practical twin pairs: `(2,4)`, `(4,6)`, `(6,8)`, `(16,18)`, `(30,32)`,
`(126,128)`, `(2046,2048)` and `(8190,8192)`. -/
theorem practicalTwin_examples :
    PracticalTwin 2 ∧ PracticalTwin 4 ∧ PracticalTwin 6 ∧ PracticalTwin 16 ∧
      PracticalTwin 30 ∧ PracticalTwin 126 ∧ PracticalTwin 2046 ∧ PracticalTwin 8190 := by
  have key : ∀ n : ℕ, DivisorComplete n → DivisorComplete (n + 2) → PracticalTwin n := by
    intro n h1 h2
    exact ⟨(isPractical_iff_divisorComplete _).2 h1, (isPractical_iff_divisorComplete _).2 h2⟩
  refine ⟨key 2 (by decide) (by decide), key 4 (by decide) (by decide),
    key 6 (by decide) (by decide), key 16 (by decide) (by decide),
    key 30 (by decide) (by decide), key 126 (by decide) (by decide),
    key 2046 (by decide) (by decide), key 8190 (by decide) (by decide)⟩

/-- The Brockian "practical twin" conjecture: there are infinitely many `n` such that both
`n` and `n + 2` are practical. -/
def PracticalTwinConjecture : Prop := ∀ N : ℕ, ∃ n > N, PracticalTwin n

/-- The practical twin conjecture is equivalent to the purely elementary (and decidable
pointwise) statement that infinitely many `n` satisfy the divisor-chain criterion at both `n`
and `n + 2`. -/
theorem practicalTwinConjecture_iff :
    PracticalTwinConjecture ↔ ∀ N : ℕ, ∃ n > N, DivisorComplete n ∧ DivisorComplete (n + 2) := by
  constructor
  · intro h N
    obtain ⟨n, hn, h1, h2⟩ := h N
    exact ⟨n, hn, (isPractical_iff_divisorComplete _).1 h1,
      (isPractical_iff_divisorComplete _).1 h2⟩
  · intro h N
    obtain ⟨n, hn, h1, h2⟩ := h N
    exact ⟨n, hn, (isPractical_iff_divisorComplete _).2 h1,
      (isPractical_iff_divisorComplete _).2 h2⟩

/-- **Conditional reduction.** The practical twin conjecture follows from the purely
elementary, decidable statement that infinitely many `n` have both `n` and `n + 2` satisfying
the divisor-chain criterion `DivisorComplete`. -/
theorem PracticalTwinInfinitude
    (h : ∀ N : ℕ, ∃ n > N, DivisorComplete n ∧ DivisorComplete (n + 2)) :
    PracticalTwinConjecture := by
  intro N
  obtain ⟨n, hn, h1, h2⟩ := h N
  exact ⟨n, hn, (isPractical_iff_divisorComplete _).2 h1, (isPractical_iff_divisorComplete _).2 h2⟩

end Brockian.PracticalNumbers

