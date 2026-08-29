/-
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian

/-- The number of distinct residue classes modulo `p` occupied by the tuple `H`.
This is the local density `ν_p(H)` appearing in the Hardy–Littlewood singular series. -/
def nu (p : ℕ) (H : Finset ℤ) : ℕ := (H.image (fun h : ℤ => (h : ZMod p))).card

/-- A finite set of integers is *admissible* if for every prime `p` it misses at least one
residue class modulo `p`. -/
def IsAdmissible (H : Finset ℤ) : Prop := ∀ p : ℕ, p.Prime → nu p H < p

/-- The local factor of the Hardy–Littlewood singular series at the prime `p`. -/
noncomputable def singularFactor (p : ℕ) (H : Finset ℤ) : ℝ :=
  (1 - (nu p H : ℝ) / p) / (1 - 1 / (p : ℝ)) ^ H.card

/-- The partial Hardy–Littlewood singular series: the product of the local factors over all
primes below `N`. -/
noncomputable def singularSeriesPartial (N : ℕ) (H : Finset ℤ) : ℝ :=
  ∏ p ∈ Nat.primesBelow N, singularFactor p H

lemma nu_le_card (p : ℕ) (H : Finset ℤ) : nu p H ≤ H.card := Finset.card_image_le

lemma nu_lt_of_card_lt {p : ℕ} {H : Finset ℤ} (h : H.card < p) : nu p H < p :=
  lt_of_le_of_lt (nu_le_card p H) h

lemma card_pair {d : ℤ} (hd : d ≠ 0) : ({0, d} : Finset ℤ).card = 2 := by
  rw [Finset.card_insert_of_notMem (by simpa using hd.symm), Finset.card_singleton]

/-- If `p` divides `d` then the pair `{0, d}` occupies a single class mod `p`. -/
lemma nu_pair_of_dvd (p : ℕ) {d : ℤ} (hd : (p : ℤ) ∣ d) : nu p ({0, d} : Finset ℤ) = 1 := by
  have h : ((d : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd d p).2 hd
  simp [nu, Finset.image_insert, h]

/-- If `p` does not divide `d` then the pair `{0, d}` occupies two classes mod `p`. -/
lemma nu_pair_of_not_dvd (p : ℕ) {d : ℤ} (hd : ¬ (p : ℤ) ∣ d) : nu p ({0, d} : Finset ℤ) = 2 := by
  have h : ((d : ℤ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hd
  rw [nu, Finset.image_insert, Finset.image_singleton]
  rw [Finset.card_insert_of_notMem (by simpa using fun hc => h hc.symm), Finset.card_singleton]

lemma nu_two_pair_of_even {d : ℤ} (hd : Even d) : nu 2 ({0, d} : Finset ℤ) = 1 :=
  nu_pair_of_dvd 2 (by exact_mod_cast hd.two_dvd)

lemma nu_two_pair_of_odd {d : ℤ} (hd : ¬ Even d) : nu 2 ({0, d} : Finset ℤ) = 2 := by
  refine nu_pair_of_not_dvd 2 ?_
  rintro ⟨k, rfl⟩
  exact hd ⟨k, by ring⟩

/-- A pair `{0, d}` with `d ≠ 0` is admissible exactly when `d` is even. -/
theorem isAdmissible_pair_iff {d : ℤ} (hd : d ≠ 0) :
    IsAdmissible ({0, d} : Finset ℤ) ↔ Even d := by
  constructor
  · intro h
    by_contra hodd
    have := h 2 Nat.prime_two
    rw [nu_two_pair_of_odd hodd] at this
    exact lt_irrefl 2 this
  · intro heven p hp
    rcases eq_or_lt_of_le hp.two_le with h2 | h2
    · rw [← h2, nu_two_pair_of_even heven]; norm_num
    · exact nu_lt_of_card_lt (by rw [card_pair hd]; omega)

/-- For an admissible tuple, every local factor of the singular series is positive. -/
theorem singularFactor_pos {H : Finset ℤ} (hH : IsAdmissible H) {p : ℕ} (hp : p.Prime) :
    0 < singularFactor p H := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hnum : 0 < 1 - (nu p H : ℝ) / p := by
    have : (nu p H : ℝ) < p := by exact_mod_cast hH p hp
    have := (div_lt_one hp0).2 this
    linarith
  have hden : 0 < 1 - 1 / (p : ℝ) := by
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have : 1 / (p : ℝ) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le <;> linarith
    linarith
  exact div_pos hnum (pow_pos hden _)

/-- Every partial singular series of an admissible tuple is positive. -/
theorem singularSeriesPartial_pos {H : Finset ℤ} (hH : IsAdmissible H) (N : ℕ) :
    0 < singularSeriesPartial N H := by
  refine Finset.prod_pos fun p hp => singularFactor_pos hH ?_
  exact (Nat.mem_primesBelow.1 hp).2

/-- Explicit local factor of a pair at a prime not dividing the gap. -/
lemma singularFactor_pair_of_not_dvd {p : ℕ} {d : ℤ} (hd0 : d ≠ 0) (hd : ¬ (p : ℤ) ∣ d) :
    singularFactor p ({0, d} : Finset ℤ) = (1 - 2 / (p : ℝ)) / (1 - 1 / (p : ℝ)) ^ 2 := by
  rw [singularFactor, nu_pair_of_not_dvd p hd, card_pair hd0]
  norm_num

/-- Explicit local factor of a pair at an odd prime dividing the gap: it equals `p / (p - 1)`. -/
lemma singularFactor_pair_of_dvd {p : ℕ} (hp : p.Prime) {d : ℤ} (hd0 : d ≠ 0)
    (hd : (p : ℤ) ∣ d) :
    singularFactor p ({0, d} : Finset ℤ) = (p : ℝ) / ((p : ℝ) - 1) := by
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hp.pos.ne'
  have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp1 : (p : ℝ) - 1 ≠ 0 := by intro h; linarith
  rw [singularFactor, nu_pair_of_dvd p hd, card_pair hd0]
  field_simp
  ring

/-- **Singular Series Gaps 13501360.**

For each gap `d` in the range `1350 ≤ d ≤ 1360`, the pair `{0, d}` is an admissible
Hardy–Littlewood tuple precisely when `d` is even; there are exactly six such admissible
gaps in this range, namely `1350, 1352, 1354, 1356, 1358, 1360`; and for each of them every
local factor of the singular series is strictly positive, hence so is every partial singular
series. -/
theorem SingularSeriesGaps13501360 :
    (∀ d ∈ Finset.Icc (1350 : ℤ) 1360, IsAdmissible ({0, d} : Finset ℤ) ↔ Even d) ∧
    (Finset.Icc (1350 : ℤ) 1360).filter
        (fun d => IsAdmissible ({0, d} : Finset ℤ)) =
      ({1350, 1352, 1354, 1356, 1358, 1360} : Finset ℤ) ∧
    ((Finset.Icc (1350 : ℤ) 1360).filter
        (fun d => IsAdmissible ({0, d} : Finset ℤ))).card = 6 ∧
    (∀ d ∈ Finset.Icc (1350 : ℤ) 1360, Even d →
      ∀ p : ℕ, p.Prime → 0 < singularFactor p ({0, d} : Finset ℤ)) ∧
    (∀ d ∈ Finset.Icc (1350 : ℤ) 1360, Even d →
      ∀ N : ℕ, 0 < singularSeriesPartial N ({0, d} : Finset ℤ)) := by
  have key : ∀ d ∈ Finset.Icc (1350 : ℤ) 1360,
      (IsAdmissible ({0, d} : Finset ℤ) ↔ Even d) := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    exact isAdmissible_pair_iff (by omega)
  have hset : (Finset.Icc (1350 : ℤ) 1360).filter
      (fun d => IsAdmissible ({0, d} : Finset ℤ)) =
      ({1350, 1352, 1354, 1356, 1358, 1360} : Finset ℤ) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hd, hadm⟩
      have he : Even d := (key d (Finset.mem_Icc.2 hd)).1 hadm
      rw [Int.even_iff] at he
      omega
    · intro h
      have hd : 1350 ≤ d ∧ d ≤ 1360 := by rcases h with h|h|h|h|h|h <;> omega
      refine ⟨hd, (key d (Finset.mem_Icc.2 hd)).2 ?_⟩
      rw [Int.even_iff]
      rcases h with h|h|h|h|h|h <;> omega
  refine ⟨key, hset, ?_, ?_, ?_⟩
  · rw [hset]; decide
  · intro d hd he p hp
    exact singularFactor_pos ((key d hd).2 he) hp
  · intro d hd he N
    exact singularSeriesPartial_pos ((key d hd).2 he) N

/-- Concrete instance: `3 ∣ 1350`, so the local factor at `3` of the gap `1350` is `3/2`. -/
theorem singularFactor_three_1350 : singularFactor 3 ({0, 1350} : Finset ℤ) = 3 / 2 := by
  rw [singularFactor_pair_of_dvd (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- Concrete instance: `7 ∤ 1350`, so the local factor at `7` of the gap `1350` is `35/36`. -/
theorem singularFactor_seven_1350 : singularFactor 7 ({0, 1350} : Finset ℤ) = 35 / 36 := by
  rw [singularFactor_pair_of_not_dvd (by norm_num) (by decide)]
  norm_num

end Brockian

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

