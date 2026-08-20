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
# Singular Series Gaps 12401250
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps12401250
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 12401250
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps12401250
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Brockian

/-- A finite set `H` of natural numbers is *admissible* (in the sense of the
Hardy–Littlewood prime `k`-tuples conjecture) if for every prime `p` the residues
of the elements of `H` modulo `p` do not cover all of `ZMod p`. -/
def Admissible (H : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r < p, ∀ h ∈ H, h % p ≠ r

/-- `localCount H p` is the number of distinct residues modulo `p` occupied by `H`.
This is the quantity `ν_H(p)` appearing in the Euler factor
`(1 - ν_H(p)/p)(1 - 1/p)^{-|H|}` of the singular series `𝔖(H)`. -/
def localCount (H : Finset ℕ) (p : ℕ) : ℕ := (H.image (· % p)).card

lemma localCount_le_card (H : Finset ℕ) (p : ℕ) : localCount H p ≤ H.card :=
  Finset.card_image_le

lemma image_mod_subset (H : Finset ℕ) {p : ℕ} (hp : 0 < p) :
    H.image (· % p) ⊆ Finset.range p := by
  intro x hx
  simp only [Finset.mem_image] at hx
  obtain ⟨y, _, rfl⟩ := hx
  exact Finset.mem_range.2 (Nat.mod_lt _ hp)

/-- Admissibility is equivalent to the statement that every local density factor
`1 - ν_H(p)/p` of the singular series is nonzero. -/
theorem admissible_iff_localCount_lt (H : Finset ℕ) :
    Admissible H ↔ ∀ p : ℕ, p.Prime → localCount H p < p := by
  constructor
  · rintro hH p hp
    obtain ⟨r, hr, hrH⟩ := hH p hp
    have hsub : H.image (· % p) ⊆ (Finset.range p).erase r := by
      intro x hx
      simp only [Finset.mem_image] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact Finset.mem_erase.2 ⟨hrH y hy, Finset.mem_range.2 (Nat.mod_lt _ hp.pos)⟩
    have := Finset.card_le_card hsub
    have hcard : ((Finset.range p).erase r).card = p - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_range.2 hr), Finset.card_range]
    have hp1 : 1 ≤ p := hp.one_lt.le.trans' (by norm_num)
    unfold localCount
    omega
  · intro h p hp
    have hlt := h p hp
    have hsub := image_mod_subset H hp.pos
    have hne : ¬ Finset.range p ⊆ H.image (· % p) := by
      intro hcon
      have := Finset.card_le_card hcon
      rw [Finset.card_range] at this
      exact absurd hlt (by unfold localCount; omega)
    rw [Finset.subset_iff] at hne
    push_neg at hne
    obtain ⟨r, hr, hrmem⟩ := hne
    refine ⟨r, Finset.mem_range.1 hr, ?_⟩
    intro x hx hxr
    exact hrmem (Finset.mem_image.2 ⟨x, hx, hxr⟩)

/-- If a prime `p` exceeds the size of `H`, the residues of `H` cannot cover `ZMod p`. -/
lemma exists_missing_residue_of_card_lt {H : Finset ℕ} {p : ℕ} (hp : 0 < p)
    (hcard : H.card < p) : ∃ r < p, ∀ h ∈ H, h % p ≠ r := by
  have hsub := image_mod_subset H hp
  have hlt : (H.image (· % p)).card < (Finset.range p).card := by
    rw [Finset.card_range]
    exact lt_of_le_of_lt Finset.card_image_le hcard
  have hne : ¬ Finset.range p ⊆ H.image (· % p) := by
    intro hcon
    exact absurd (Finset.card_le_card hcon) (by omega)
  rw [Finset.subset_iff] at hne
  push_neg at hne
  obtain ⟨r, hr, hrmem⟩ := hne
  refine ⟨r, Finset.mem_range.1 hr, ?_⟩
  intro x hx hxr
  exact hrmem (Finset.mem_image.2 ⟨x, hx, hxr⟩)

/-- To check admissibility of a set of size at most `7` it suffices to check the
primes `2, 3, 5, 7`. -/
lemma admissible_of_small_primes {H : Finset ℕ} (hcard : H.card ≤ 7)
    (h : ∀ p : ℕ, p ≤ 7 → p.Prime → ∃ r < p, ∀ x ∈ H, x % p ≠ r) : Admissible H := by
  intro p hp
  by_cases hle : p ≤ 7
  · exact h p hle hp
  · exact exists_missing_residue_of_card_lt hp.pos (by omega)

lemma not_admissible_of_prime {H : Finset ℕ} {p : ℕ} (hp : p.Prime)
    (h : ¬ ∃ r < p, ∀ x ∈ H, x % p ≠ r) : ¬ Admissible H :=
  fun hA => h (hA p hp)

/-- The `7`-element candidate tuple with base pattern `{0, 4, 6, 10, 12, 16}`
and a final entry at distance `n` from the first one. -/
def gapTuple (n : ℕ) : Finset ℕ := {0, 4, 6, 10, 12, 16, n}

lemma card_gapTuple_le (n : ℕ) : (gapTuple n).card ≤ 7 := by
  unfold gapTuple
  have h1 := Finset.card_insert_le 0 ({4, 6, 10, 12, 16, n} : Finset ℕ)
  have h2 := Finset.card_insert_le 4 ({6, 10, 12, 16, n} : Finset ℕ)
  have h3 := Finset.card_insert_le 6 ({10, 12, 16, n} : Finset ℕ)
  have h4 := Finset.card_insert_le 10 ({12, 16, n} : Finset ℕ)
  have h5 := Finset.card_insert_le 12 ({16, n} : Finset ℕ)
  have h6 := Finset.card_insert_le 16 ({n} : Finset ℕ)
  have h7 : ({n} : Finset ℕ).card = 1 := Finset.card_singleton n
  omega

lemma admissible_gapTuple_1242 : Admissible (gapTuple 1242) := by
  refine admissible_of_small_primes (card_gapTuple_le _) ?_
  intro p hp hpp
  interval_cases p <;> first
    | exact absurd hpp (by decide)
    | (unfold gapTuple; decide)

lemma admissible_gapTuple_1246 : Admissible (gapTuple 1246) := by
  refine admissible_of_small_primes (card_gapTuple_le _) ?_
  intro p hp hpp
  interval_cases p <;> first
    | exact absurd hpp (by decide)
    | (unfold gapTuple; decide)

/-- **Singular Series Gaps 1240–1250.**

Among the eleven gap widths `n` with `1240 ≤ n ≤ 1250`, the seven-element tuple
`{0, 4, 6, 10, 12, 16, n}` is admissible — equivalently, its singular series
`𝔖` is nonzero — exactly for `n = 1242` and `n = 1246`. -/
theorem SingularSeriesGaps12401250 (n : ℕ) (hn : n ∈ Finset.Icc 1240 1250) :
    Admissible (gapTuple n) ↔ (n = 1242 ∨ n = 1246) := by
  simp only [Finset.mem_Icc] at hn
  obtain ⟨h1, h2⟩ := hn
  interval_cases n
  · exact iff_of_false
      (not_admissible_of_prime (p := 7) (by norm_num) (by unfold gapTuple; decide))
      (by norm_num)
  · exact iff_of_false
      (not_admissible_of_prime (p := 2) (by norm_num) (by unfold gapTuple; decide))
      (by norm_num)
  · exact iff_of_true admissible_gapTuple_1242 (by norm_num)
  · exact iff_of_false
      (not_admissible_of_prime (p := 2) (by norm_num) (by unfold gapTuple; decide))
      (by norm_num)
  · exact iff_of_false
      (not_admissible_of_prime (p := 3) (by norm_num) (by unfold gapTuple; decide))
      (by norm_num)
  · exact iff_of_false
      (not_admissible_of_prime (p := 2) (by norm_num) (by unfold gapTuple; decide))
      (by norm_num)
  · exact iff_of_true admissible_gapTuple_1246 (by norm_num)
  · exact iff_of_false
      (not_admissible_of_prime (p := 2) (by norm_num) (by unfold gapTuple; decide))
      (by norm_num)
  · exact iff_of_false
      (not_admissible_of_prime (p := 5) (by norm_num) (by unfold gapTuple; decide))
      (by norm_num)
  · exact iff_of_false
      (not_admissible_of_prime (p := 2) (by norm_num) (by unfold gapTuple; decide))
      (by norm_num)
  · exact iff_of_false
      (not_admissible_of_prime (p := 3) (by norm_num) (by unfold gapTuple; decide))
      (by norm_num)

/-- For an admissible tuple every Euler factor of the singular series is positive. -/
theorem singularSeries_factor_pos {H : Finset ℕ} (hH : Admissible H) (p : ℕ)
    (hp : p.Prime) : 0 < 1 - (localCount H p : ℝ) / p := by
  have hlt : localCount H p < p := (admissible_iff_localCount_lt H).1 hH p hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have : (localCount H p : ℝ) / p < 1 := by
    rw [div_lt_one hp0]
    exact_mod_cast hlt
  linarith

/-- Consequently the singular series of the two new admissible gap tuples
in the range `1240 ≤ n ≤ 1250` has all its local factors positive. -/
theorem singularSeries_factor_pos_gapTuple (n : ℕ) (hn : n = 1242 ∨ n = 1246)
    (p : ℕ) (hp : p.Prime) : 0 < 1 - (localCount (gapTuple n) p : ℝ) / p := by
  rcases hn with rfl | rfl
  · exact singularSeries_factor_pos admissible_gapTuple_1242 p hp
  · exact singularSeries_factor_pos admissible_gapTuple_1246 p hp

end Brockian

