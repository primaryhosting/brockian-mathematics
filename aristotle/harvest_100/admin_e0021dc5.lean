/-
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian

/-- The number of residue classes modulo `p` occupied by a finite set `H` of natural numbers.
This is the quantity `ν_H(p)` appearing in the Euler factors of the Hardy–Littlewood
singular series of the tuple `H`. -/
def resCount (H : Finset ℕ) (p : ℕ) : ℕ := (H.image (· % p)).card

/-- A finite set `H ⊆ ℕ` (a "gap pattern") is *admissible* when, for every prime `p`, some
residue class modulo `p` is missed by `H`. Equivalently, every Euler factor of the singular
series of `H` is nonzero. -/
def Admissible (H : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r < p, ∀ h ∈ H, h % p ≠ r

/-- Admissibility is exactly the statement that `ν_H(p) < p` for every prime `p`. -/
theorem admissible_iff_resCount_lt (H : Finset ℕ) :
    Admissible H ↔ ∀ p : ℕ, p.Prime → resCount H p < p := by
  constructor
  · intro hH p hp
    obtain ⟨r, hrp, hr⟩ := hH p hp
    have hsub : H.image (· % p) ⊆ (Finset.range p).erase r := by
      intro x hx
      simp only [Finset.mem_image] at hx
      obtain ⟨h, hh, rfl⟩ := hx
      exact Finset.mem_erase.2 ⟨hr h hh, Finset.mem_range.2 (Nat.mod_lt _ hp.pos)⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_range.2 hrp), Finset.card_range] at this
    have hp1 : 1 ≤ p := hp.one_lt.le.trans_eq' (by norm_num)
    exact lt_of_le_of_lt this (by omega)
  · intro hH p hp
    have hlt : (H.image (· % p)).card < p := hH p hp
    have hsub : H.image (· % p) ⊆ Finset.range p := by
      intro x hx
      simp only [Finset.mem_image] at hx
      obtain ⟨h, _, rfl⟩ := hx
      exact Finset.mem_range.2 (Nat.mod_lt _ hp.pos)
    have hne : H.image (· % p) ≠ Finset.range p := by
      intro h
      rw [h, Finset.card_range] at hlt
      exact lt_irrefl _ hlt
    obtain ⟨r, hr, hrmem⟩ := Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.2 ⟨hsub, hne⟩)
    refine ⟨r, Finset.mem_range.1 hr, ?_⟩
    intro h hh hmod
    exact hrmem (Finset.mem_image.2 ⟨h, hh, hmod⟩)

/-- A prime larger than the cardinality of `H` can never be covered by `H`. -/
theorem exists_missed_residue_of_card_lt (H : Finset ℕ) {p : ℕ} (hp : 0 < p)
    (hcard : H.card < p) : ∃ r < p, ∀ h ∈ H, h % p ≠ r := by
  have hsub : H.image (· % p) ⊆ Finset.range p := by
    intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨h, _, rfl⟩ := hx
    exact Finset.mem_range.2 (Nat.mod_lt _ hp)
  have hlt : (H.image (· % p)).card < (Finset.range p).card := by
    rw [Finset.card_range]
    exact lt_of_le_of_lt (Finset.card_image_le) hcard
  have hne : H.image (· % p) ≠ Finset.range p := fun h => by
    rw [h] at hlt; exact lt_irrefl _ hlt
  obtain ⟨r, hr, hrmem⟩ := Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.2 ⟨hsub, hne⟩)
  refine ⟨r, Finset.mem_range.1 hr, ?_⟩
  intro h hh hmod
  exact hrmem (Finset.mem_image.2 ⟨h, hh, hmod⟩)

/-- Admissibility is a *finite* condition: it suffices to check the primes `p ≤ |H|`. -/
theorem admissible_of_small_primes (H : Finset ℕ)
    (h : ∀ p ∈ Finset.range (H.card + 1), Nat.Prime p → ∃ r ∈ Finset.range p,
      ∀ x ∈ H, x % p ≠ r) :
    Admissible H := by
  intro p hp
  by_cases hle : p ≤ H.card
  · obtain ⟨r, hr, hx⟩ := h p (Finset.mem_range.2 (by omega)) hp
    exact ⟨r, Finset.mem_range.1 hr, hx⟩
  · exact exists_missed_residue_of_card_lt H hp.pos (by omega)

/-- Admissibility is invariant under translation of the gap pattern. -/
theorem admissible_image_add {H : Finset ℕ} (hH : Admissible H) (n : ℕ) :
    Admissible (H.image (· + n)) := by
  intro p hp
  obtain ⟨r, hrp, hr⟩ := hH p hp
  refine ⟨(r + n) % p, Nat.mod_lt _ hp.pos, ?_⟩
  intro h hh
  simp only [Finset.mem_image] at hh
  obtain ⟨x, hx, rfl⟩ := hh
  intro hcon
  have : x % p = r % p := by
    have := Nat.ModEq.add_right_cancel' n (show (x + n) ≡ (r + n) [MOD p] by
      simpa [Nat.ModEq, Nat.add_mod_right] using hcon)
    simpa [Nat.ModEq] using this
  rw [Nat.mod_eq_of_lt hrp] at this
  exact hr x hx this

/-- The base pattern: an admissible `9`-tuple of diameter `30`. -/
def base9 : Finset ℕ := {0, 2, 6, 8, 12, 18, 20, 26, 30}

theorem base9_card : base9.card = 9 := by decide

theorem base9_admissible : Admissible base9 := by
  apply admissible_of_small_primes
  rw [base9_card]
  decide

/-- **Singular Series Gaps 9098.**

The `9`-element gap pattern `H = {0, 2, 6, 8, 12, 18, 20, 26, 30}` and *every* one of its
translates `H + n` is admissible: for each prime `p` some residue class mod `p` is omitted,
so the number of occupied classes satisfies `ν(p) < p` and each Euler factor
`1 - ν(p)/p` of the Hardy–Littlewood singular series is strictly positive.  Consequently the
pattern yields admissible gap ranges `[n, n+30]` starting at arbitrarily large `n`. -/
theorem SingularSeriesGaps9098 :
    ∀ n : ℕ,
      (base9.image (· + n)).card = 9 ∧
      Admissible (base9.image (· + n)) ∧
      (∀ p : ℕ, p.Prime → resCount (base9.image (· + n)) p < p) ∧
      (∀ p : ℕ, p.Prime →
        0 < 1 - (resCount (base9.image (· + n)) p : ℝ) / (p : ℝ)) := by
  intro n
  have hadm : Admissible (base9.image (· + n)) := admissible_image_add base9_admissible n
  have hnu : ∀ p : ℕ, p.Prime → resCount (base9.image (· + n)) p < p :=
    (admissible_iff_resCount_lt _).1 hadm
  refine ⟨?_, hadm, hnu, ?_⟩
  · rw [Finset.card_image_of_injective _ (fun a b h => by omega), base9_card]
  · intro p hp
    have h1 : (resCount (base9.image (· + n)) p : ℝ) < (p : ℝ) := by
      exact_mod_cast hnu p hp
    have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
    have : (resCount (base9.image (· + n)) p : ℝ) / (p : ℝ) < 1 :=
      (div_lt_one hppos).2 h1
    linarith

end Brockian

